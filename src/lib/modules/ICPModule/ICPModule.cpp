/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
/*
 * @file   ICPModule.cpp
 * @author Stefan Schupp <stefan.schupp@rwth-aachen.de>
 *
 * Created on October 16, 2012, 1:07 PM
 */

#include <map>
#include <iomanip>
#include "ICPModule.h"
#include "assert.h"

using namespace std;
using namespace carl;

//#define ICP_MODULE_DEBUG_0
//#define ICP_MODULE_DEBUG_1
#define ICP_CONSIDER_WIDTH
//#define ICP_SIMPLE_VALIDATION
#define ICP_PROLONG_CONTRACTION

namespace smtrat
{
    /**
     * Constructor
     */
    ICPModule::ICPModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings* , Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mActiveNonlinearConstraints(),
        mActiveLinearConstraints(),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mVariables(),
        mIntervals(),
        mIcpRelevantCandidates(),
        mLinearizations(),
        mDeLinearizations(),
        mVariableLinearizations(),
        mSubstitutions(),
        //#ifdef BOXMANAGEMENT
        mHistoryRoot(new icp::HistoryNode(mIntervals,1)),
        mHistoryActual(NULL),
        //#endif
        mValidationFormula(new ModuleInput()),
        mLRAFoundAnswer( vector< std::atomic_bool* >( 1, new std::atomic_bool( false ) ) ),
        mLraRuntimeSettings(new RuntimeSettings),
        mLRA(MT_LRAModule, mValidationFormula, mLraRuntimeSettings, mLRAFoundAnswer),
        mCenterConstraints(),
        mCreatedDeductions(),
        mLastCandidate(NULL),
        #ifndef BOXMANAGEMENT
        mBoxStorage(),
        #endif
        mIsIcpInitialized(false),
        mCurrentId(1),
        mIsBackendCalled(false),
        mTargetDiameter(0.1),
        mContractionThreshold(0.01),
        mCountBackendCalls(0)
    {
        #ifdef ICP_BOXLOG
        icpLog.open ("icpLog.txt", ios::out | ios::trunc );
        #endif
    }

    /**
     * Destructor:
     */
    ICPModule::~ICPModule()
    {
        mLRAFoundAnswer.clear();
        delete mLraRuntimeSettings;
        #ifdef BOXMANAGEMENT
        delete mHistoryRoot;
        #endif
        delete mValidationFormula;
        mLRAFoundAnswer.clear();
        
        for(auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt)
            delete (*variableIt).second;
        
        mVariables.clear();
        #ifdef ICP_BOXLOG
        if ( icpLog.is_open() )
        {
            icpLog.close();
        }
        #endif
    }

    bool ICPModule::inform( const FormulaT& _constraint )
    {
        #ifdef ICP_MODULE_DEBUG_0
        cout << "[ICP] inform: " << _constraint << endl;
        #endif  
        if( _constraint.getType() == FormulaType::CONSTRAINT )
        {
            const ConstraintT& constraint = _constraint.constraint();
            // do not inform about boundary constraints - this leads to confusion
            if ( !constraint.isBound() )
                Module::inform( _constraint );

            unsigned constraintConsistency = constraint.isConsistent();

            if( constraintConsistency == 2 )
            {
                addConstraint( _constraint );
            }
            return constraintConsistency != 0;
        }
        return true;
    }

    bool ICPModule::assertSubformula( ModuleInput::const_iterator _formula )
    {
        Module::assertSubformula( _formula );
        switch( _formula->formula().getType() )
        {
            case FormulaType::FALSE:
            {
                std::set<FormulaT> infSubSet;
                infSubSet.insert( _formula->formula() );
                mInfeasibleSubsets.push_back( infSubSet );
                mFoundSolution.clear();
                return false;
            }
            case FormulaType::TRUE:
            {
                return true;
            }
            case FormulaType::CONSTRAINT:
            {
                const ConstraintT& constr = _formula->formula().constraint();
                // create and initialize slackvariables
                if( constr.satisfiedBy( mFoundSolution ) != 1 )
                {
                    mFoundSolution.clear();
                }
                if( !mIsIcpInitialized )
                {
                    // catch deductions
                    mLRA.init();
                    mLRA.updateDeductions();
                    while( !mLRA.deductions().empty() )
                    {
                        #ifdef ICP_MODULE_DEBUG_1
                        cout << "Create deduction for: " << mLRA.deductions().back()->toString(false,0,"",true,true,true ) << endl;
                        #endif
                        FormulaT deduction = transformDeductions( mLRA.deductions().back() );
                        mCreatedDeductions.insert(deduction);
                        mLRA.rDeductions().pop_back();
                        addDeduction(deduction);
                        #ifdef ICP_MODULE_DEBUG_1
                        cout << "Passed deduction: " << deduction->toString(false,0,"",true,true,true ) << endl;
                        #endif
                    }
                    mIsIcpInitialized = true;
                }
                #ifdef ICP_MODULE_DEBUG_0
                cout << "[ICP] Assertion: " << constr << endl;
                #endif
                if( !_formula->formula().constraint().isBound() )
                {
                    // TODO: here or somewhere later in isConsistent: remove constraints from passed formula which are implied by the current box
                    addSubformulaToPassedFormula( _formula->formula(), _formula->formula() );
                }

                // activate associated nonlinear contraction candidates
                if( !constr.lhs().isLinear() )
                {
                    activateNonlinearConstraint( _formula->formula() );
                }
                // lookup corresponding linearization - in case the constraint is already linear, mReplacements holds the constraint as the linearized one
                auto replacementIt = mLinearizations.find( _formula->formula() );
                assert( replacementIt != mLinearizations.end() );
                const FormulaT& replacementPtr = (*replacementIt).second;
                assert( replacementPtr.getType() == CONSTRAINT );
                if( replacementPtr.constraint().isBound() )
                {
                    // considered constraint is activated but has no slack variable -> it is a boundary constraint
                    auto res = mValidationFormula->add( replacementPtr );
                    #ifdef ICP_MODULE_DEBUG_0
                    cout << "[mLRA] Assert bound constraint: " << replacementPtr << endl;
                    #endif
                    // If the constraint has not yet been part of the lramodule's received formula, assert it. If the
                    // lramodule already detects inconsistency, process its infeasible subsets.
                    if( res.second && !mLRA.assertSubformula( res.first ) ) 
                    {
                        remapAndSetLraInfeasibleSubsets();
                        assert( !mInfeasibleSubsets.empty() );
                        return false;
                    }
                }
                else
                {
                    activateLinearConstraint( replacementPtr, _formula->formula() );
                }
                return true;
            }
            default:
                return true;
        }
        return true;
    }

    void ICPModule::removeSubformula( ModuleInput::const_iterator _formula )
    {
        if( _formula->formula().getType() != FormulaType::CONSTRAINT )
        {
            Module::removeSubformula( _formula );
            return;
        }
        const ConstraintT* constr = _formula->formula().pConstraint();
        #ifdef ICP_MODULE_DEBUG_0
        cout << "[ICP] Remove Formula " << *constr << endl;
        #endif
        assert( constr->isConsistent() == 2 );
        // is it nonlinear?
        auto iter = mNonlinearConstraints.find( constr );
        if( iter != mNonlinearConstraints.end() )
        {
            #ifdef ICP_MODULE_DEBUG_0
            cout << "Nonlinear." << endl;
            #endif
            for( icp::ContractionCandidate* cc : iter->second )
            {
                // remove candidate if counter == 1, else decrement counter.
                assert( cc->isActive() );
                // remove origin, no matter if constraint is active or not
                cc->removeOrigin( _formula->formula() );
                if( cc->activity() == 0 )
                {
                    // reset History to point before this candidate was used
                    resetHistory( cc );
                    // clean up icpRelevantCandidates
                    removeCandidateFromRelevant( cc );
                    mActiveNonlinearConstraints.erase( cc );
                }
            }
        }
        // linear handling
        auto linearization = mLinearizations.find( _formula->formula() );
        assert( linearization != mLinearizations.end() );
        const LRAVariable* slackvariable = mLRA.getSlackVariable( linearization->second );
        assert( slackvariable != NULL );

        // lookup if contraction candidates already exist - if so, add origins
        auto iterB = mLinearConstraints.find( slackvariable );
        if( iterB != mLinearConstraints.end() )
        {
            #ifdef ICP_MODULE_DEBUG_0
            cout << "Linear." << endl;
            #endif
            for( icp::ContractionCandidate* cc : iterB->second )
            {
                // remove candidate if counter == 1, else decrement counter.
                assert( cc->isActive() );
                // remove origin, no matter if constraint is active or not
                cc->removeOrigin( _formula->formula() );
                if( cc->activity() == 0 )
                {
                    // reset History to point before this candidate was used
                    resetHistory( cc );
                    // clean up icpRelevantCandidates
                    removeCandidateFromRelevant( cc );
                    mActiveLinearConstraints.erase( cc );
                }
            }
        }
        // remove constraint from mLRA module
        auto replacementIt = mLinearizations.find( _formula->formula() );
        assert( replacementIt != mLinearizations.end() );
        auto validationFormulaIt = mValidationFormula->find( replacementIt->first );
        if( validationFormulaIt != mValidationFormula->end() )
        {
            #ifdef ICP_MODULE_DEBUG_0
            cout << "[mLRA] remove " << validationFormulaIt->formula().constraint() << endl;
            #endif
            mLRA.removeSubformula( validationFormulaIt );
            mValidationFormula->erase( validationFormulaIt );
        }
        Module::removeSubformula( _formula );
    }

    Answer ICPModule::isConsistent()
    {
        #ifdef ICP_MODULE_DEBUG_0
        cout << "Start consistency check with the ICPModule on the constraints " << endl;
        printReceivedFormula();
        cout << "giving the intervals" << endl;
        printIntervals(true);
        #endif
        mInfeasibleSubsets.clear(); // Dirty! Normally this shouldn't be neccessary
        if( !mFoundSolution.empty() )
        {
            #ifdef ICP_MODULE_DEBUG_0
            cout << "Found solution still feasible." << endl;
            #endif
            return foundAnswer( True );
        }
        mIsBackendCalled = false;

        // Debug Outputs of linear and nonlinear Tables
        #ifdef ICP_MODULE_DEBUG_0
//        debugPrint();
        printAffectedCandidates();
        printIcpVariables();
        cout << "Id selected box: " << mHistoryRoot->id() << " Size subtree: " << mHistoryRoot->sizeSubtree() << endl;
        #endif
        Answer lraAnswer = Unknown;
        if( initialLinearCheck( lraAnswer ) )
        {
            return foundAnswer( lraAnswer );
        }
            
        #ifdef ICP_BOXLOG
        icpLog << "startTheoryCall";
        writeBox();
        #endif
        #ifdef ICP_MODULE_DEBUG_0
        printIntervals(true);
        cout << "---------------------------------------------" << endl;
        #endif
        for( ; ; )
        {
            bool splitOccurred = false;
            bool invalidBox = contractCurrentBox( splitOccurred );
            #ifdef ICP_MODULE_DEBUG_0
            cout << endl << "contract to:" << endl;
            printIntervals(true);
            cout << endl;
            #endif
            // when one interval is empty, we can skip validation and chose next box.
            if( invalidBox ) // box contains no solution
            {
                #ifdef BOXMANAGEMENT
                // choose next box
                #ifdef ICP_MODULE_DEBUG_0
                cout << "Generated empty interval, Chose new box: " << endl;
                #endif
                if( mLastCandidate != NULL) // if there has been a candidate, the stateInfeasible set has to be created, otherwise it has been generated during checkBoxAgainstLinear...
                {
                    assert(mVariables.find(mLastCandidate->derivationVar()) != mVariables.end());
                    mHistoryActual->addInfeasibleVariable( mVariables.at(mLastCandidate->derivationVar()) );
                    if (mHistoryActual->rReasons().find(mLastCandidate->derivationVar()) != mHistoryActual->rReasons().end())
                    {
                        for( auto constraintIt = mHistoryActual->rReasons().at(mLastCandidate->derivationVar()).begin(); constraintIt != mHistoryActual->rReasons().at(mLastCandidate->derivationVar()).end(); ++constraintIt )
                            mHistoryActual->addInfeasibleConstraint(*constraintIt);
                    }
                }
                if( !chooseBox() )
                    return foundAnswer(False);
                #else
                #ifdef ICP_MODULE_DEBUG_0
                cout << "Whole box contains no solution! Return False." << endl;
                #endif
                // whole box forms infeasible subset
                mInfeasibleSubsets.push_back( createPremiseDeductions() );
//                printReceivedFormula();
//                printInfeasibleSubsets();
                return foundAnswer( False );
                #endif
            }
            else
            {
                assert( !intervalsEmpty() );
                #ifndef BOXMANAGEMENT
                if( splitOccurred )
                {
                    #ifdef ICP_MODULE_DEBUG_0
                    cout << "Return unknown, raise deductions for split." << endl;
                    #endif
                    return foundAnswer( Unknown );
                }
                #endif
                if( tryTestPoints() )
                {
                    return foundAnswer( True );
                }
                else
                {
                    // create Bounds and set them, add to passedFormula
                    pushBoundsToPassedFormula();
                    // call backends on found box
                    return foundAnswer( callBackends() );
                }
            }
        }
        assert( false ); // This should not happen!
        return foundAnswer( Unknown );
    }
    
    void ICPModule::resetHistory( icp::ContractionCandidate* _cc )
    {
        // reset History to point before this candidate was used
        icp::HistoryNode::set_HistoryNode nodes = mHistoryRoot->findCandidates( _cc );
        // as the set is sorted ascending by id, we pick the node with the lowest id
        if( !nodes.empty() )
        {
            icp::HistoryNode* firstNode = (*nodes.begin())->parent();
            if ( *firstNode == *mHistoryRoot )
                firstNode = mHistoryRoot->addRight( new icp::HistoryNode( mHistoryRoot->intervals(), 2 ) );

            setBox(firstNode);
            mHistoryActual->reset();
        }
    }
    
    void ICPModule::addConstraint( const FormulaT& _formula )
    {
        assert( _formula.getType() == FormulaType::CONSTRAINT );
        assert( _formula.constraint().isConsistent() == 2 );
        const ConstraintT& constraint = _formula.constraint();
        auto linearization = mLinearizations.find( _formula );
        if( linearization == mLinearizations.end() ) // If this constraint has not been added before
        {
            const Poly& constr = constraint.lhs();
            // add original variables to substitution mapping
            for( auto var = constraint.variables().begin(); var != constraint.variables().end(); ++var )
            {
                if( mSubstitutions.find( *var ) == mSubstitutions.end() )
                {
                    assert( mVariables.find(*var) == mVariables.end() );
                    assert( mIntervals.find(*var) == mIntervals.end() );
                    mSubstitutions.insert( std::make_pair( *var, Poly(*var) ) );
                    getIcpVariable( *var, true, NULL ); // note that we have to set the lra variable later
                    mHistoryRoot->addInterval( *var, smtrat::DoubleInterval::unboundedInterval() );
                }
            }
            // actual preprocessing
            FormulaT linearFormula;
            if( constr.isLinear() )
            {
                linearFormula = _formula;
            }
            else
            {
                assert( mLinearizations.find( _formula ) == mLinearizations.end() );
                vector<Poly> temporaryMonomes = icp::getNonlinearMonomials( constr );
                assert( !temporaryMonomes.empty() );
                Poly lhs = createNonlinearCCs( _formula.pConstraint(), temporaryMonomes );
                linearFormula = FormulaT( lhs, constraint.relation() );
                assert( linearFormula.constraint().lhs().isLinear() );
                #ifdef ICP_MODULE_DEBUG_0
                cout << "linearize constraint to   " << linearFormula.constraint() << endl;
                #endif
            };
            assert( !linearFormula.isTrue() );
            // store replacement for later comparison when asserting
            assert( mDeLinearizations.find( linearFormula ) == mDeLinearizations.end() );
            assert( mLinearizations.find( _formula ) == mLinearizations.end() );
            mDeLinearizations[linearFormula] = _formula;
            mLinearizations[_formula] = linearFormula;
            // inform internal LRAmodule of the linearized constraint
            mLRA.inform( linearFormula );
            const ConstraintT& linearizedConstraint = linearFormula.constraint();
            #ifdef ICP_MODULE_DEBUG_0
            cout << "[mLRA] inform: " << linearizedConstraint << endl;
            #endif
            
            if( !linearizedConstraint.isBound() )
            {
                createLinearCCs( linearFormula, _formula );
            }
            
            // set the lra variables for the icp variables regarding variables (introduced and original ones)
            // TODO: Refactor this last part - it seems to be too complicated
            for( auto var = linearizedConstraint.variables().begin(); var != linearizedConstraint.variables().end(); ++var )
            {
                auto iter = mVariables.find( *var );
                assert( iter != mVariables.end() );
                if( iter->second->lraVar() == NULL )
                {
                    auto ovarIter = mLRA.originalVariables().find( *var );
                    if( ovarIter != mLRA.originalVariables().end() )
                    {
                        iter->second->setLraVar( ovarIter->second );
                    }
                }
            }
        }
    }
    
    icp::IcpVariable* ICPModule::getIcpVariable( carl::Variable::Arg _var, bool _original, const LRAVariable* _lraVar )
    {
        auto iter = mVariables.find( _var );
        if( iter != mVariables.end() )
        {
            return iter->second;
        }
        auto res = mIntervals.insert( std::make_pair( _var, smtrat::DoubleInterval::unboundedInterval() ) );
        assert( res.second );
        icp::IcpVariable* icpVar = new icp::IcpVariable( _var, _original, passedFormulaEnd(), res.first, _lraVar );
        mVariables.insert( std::make_pair( _var, icpVar ) );
        return icpVar;
    }
    
    void ICPModule::activateNonlinearConstraint( const FormulaT& _formula )
    {
        assert( _formula.getType() == FormulaType::CONSTRAINT );
        auto iter = mNonlinearConstraints.find( _formula.pConstraint() );
        #ifdef ICP_MODULE_DEBUG_0
        cout << "[ICP] Assertion (nonlinear)" << _formula.constraint() <<  endl;
        cout << "mNonlinearConstraints.size: " << mNonlinearConstraints.size() << endl;
        cout << "Number Candidates: " << iter->second.size() << endl;
        #endif
        for( auto candidateIt = iter->second.begin(); candidateIt != iter->second.end(); ++candidateIt )
        {
            if( (*candidateIt)->activity() == 0 )
            {
                mActiveNonlinearConstraints.insert( *candidateIt );
                #ifdef ICP_MODULE_DEBUG_0
                cout << "[ICP] Activated candidate: ";
                (*candidateIt)->print();
                #endif
            }
            (*candidateIt)->addOrigin( _formula );
            #ifdef ICP_MODULE_DEBUG_0
            cout << "[ICP] Increased candidate count: ";
            (*candidateIt)->print();
            #endif
        }
    }
    
    void ICPModule::activateLinearConstraint( const FormulaT& _formula, const FormulaT& _origin )
    {
        assert( _formula.getType() == FormulaType::CONSTRAINT );
        const LRAVariable* slackvariable = mLRA.getSlackVariable( _formula );
        assert( slackvariable != NULL );

        // lookup if contraction candidates already exist - if so, add origins
        auto iter = mLinearConstraints.find( slackvariable );
        assert( iter != mLinearConstraints.end() );
        for ( auto candidateIt = iter->second.begin(); candidateIt != iter->second.end(); ++candidateIt )
        {
            #ifdef ICP_MODULE_DEBUG_1
            cout << "[ICP] ContractionCandidates already exist: ";
            slackvariable->print();
            cout << ", Size Origins: " << (*candidateIt)->origin().size() << endl;
            cout << _formula << endl;
            (*candidateIt)->print();
            cout << "Adding origin." << endl;
            #endif

            // set value in activeLinearConstraints
            if( (*candidateIt)->activity() == 0 )
            {
                mActiveLinearConstraints.insert( *candidateIt );
            }
            
            // add origin
            (*candidateIt)->addOrigin( _origin );
        }

        // assert in mLRA
        auto res = mValidationFormula->add( _formula );
        if( res.second )
        {
            if( !mLRA.assertSubformula( res.first ) )
            {
                remapAndSetLraInfeasibleSubsets();
            }
            #ifdef ICP_MODULE_DEBUG_0
            cout << "[mLRA] Assert " << _formula << endl;
            #endif
        }
    }
    
    bool ICPModule::initialLinearCheck( Answer& _answer )
    {
        #ifdef ICP_MODULE_DEBUG_0
        cout << "Initial linear check:" << endl;
        #endif
        // call mLRA to check linear feasibility
        mLRA.clearDeductions();
        mLRA.rReceivedFormula().updateProperties();
        _answer = mLRA.isConsistent();
        
        // catch deductions
        mLRA.updateDeductions();
        while( !mLRA.deductions().empty() )
        {
            #ifdef ICP_MODULE_DEBUG_1
            cout << "Create deduction for: " << *mLRA.deductions().back() << endl;
            #endif
            FormulaT deduction = transformDeductions(mLRA.deductions().back());
            mLRA.rDeductions().pop_back();
            addDeduction(deduction);
            #ifdef ICP_MODULE_DEBUG_1   
            cout << "Passed deduction: " << deduction << endl;
            #endif
        }
        mLRA.clearDeductions();
        if( _answer == False )
        {
            // remap infeasible subsets to original constraints
            remapAndSetLraInfeasibleSubsets();
            #ifdef ICP_MODULE_DEBUG_0
            cout << "LRA: " << _answer << endl;
            #endif
            return true;
        }
        else if( _answer == Unknown )
        {
            #ifdef ICP_MODULE_DEBUG_0
            mLRA.printReceivedFormula();
            cout << "LRA: " << _answer << endl;
            #endif
            return true;
        }
        else if( mActiveNonlinearConstraints.empty() ) // _answer == True, but no nonlinear constraints -> linear solution is a solution
        {
            #ifdef ICP_MODULE_DEBUG_0
            cout << "LRA: " << _answer << endl;
            #endif
            mFoundSolution = mLRA.getRationalModel();
            return true;
        }
        else // _answer == True
        {
            // get intervals for initial variables
            EvalRationalIntervalMap tmp = mLRA.getVariableBounds();
            #ifdef ICP_MODULE_DEBUG_0
            cout << "Newly obtained Intervals: " << endl;
            #endif
            for ( auto constraintIt = tmp.begin(); constraintIt != tmp.end(); ++constraintIt )
            {
                #ifdef ICP_MODULE_DEBUG_0
                cout << (*constraintIt).first << ": " << (*constraintIt).second << endl;
                #endif
                assert( mVariables.find(constraintIt->first) != mVariables.end() );
                icp::IcpVariable& icpVar = *mVariables.find((*constraintIt).first)->second;
                RationalInterval tmp = (*constraintIt).second;
                DoubleInterval newInterval = DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType());
                mHistoryRoot->addInterval((*constraintIt).first, newInterval );
                icpVar.setInterval( newInterval );
            }
            
            // get intervals for slackvariables
            const LRAModule<LRASettings1>::ExVariableMap slackVariables = mLRA.slackVariables();
            for( auto slackIt = slackVariables.begin(); slackIt != slackVariables.end(); ++slackIt )
            {
                std::map<const LRAVariable*, ContractionCandidates>::iterator linIt = mLinearConstraints.find((*slackIt).second);
                if ( linIt != mLinearConstraints.end() )
                {
                    // dirty hack: expect lhs to be set and take first item of set of CCs --> Todo: Check if it is really set in the constructors of the CCs during inform and assert
                    RationalInterval tmp = (*slackIt).second->getVariableBounds();
                    // keep root updated about the initial box.
                    mHistoryRoot->rIntervals()[(*(*linIt).second.begin())->lhs()] = smtrat::DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType());
                    // No need to propagate update-status in the icp-variable
                    assert( mIntervals.find( (*(*linIt).second.begin())->lhs() ) != mIntervals.end() );
                    mIntervals[(*(*linIt).second.begin())->lhs()] = smtrat::DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType());
                    #ifdef ICP_MODULE_DEBUG_1
                    cout << "Added interval (slackvariables): " << (*(*linIt).second.begin())->lhs() << " " << tmp << endl;
                    #endif
                }
            }
            // temporary solution - an added linear constraint might have changed the box.
            setBox(mHistoryRoot);
            mHistoryRoot->rReasons().clear();
            mHistoryRoot->rStateInfeasibleConstraints().clear();
            mHistoryRoot->rStateInfeasibleVariables().clear();
            mHistoryActual = mHistoryActual->addRight( new icp::HistoryNode( mIntervals, 2 ) );
            mCurrentId = mHistoryActual->id();
            #ifdef ICP_MODULE_DEBUG_0
            cout << "Id actual box: " << mHistoryActual->id() << " Size subtree: " << mHistoryActual->sizeSubtree() << endl;
            #endif
            return false;
        }
    }
    
    bool ICPModule::contractCurrentBox( bool& _splitOccurred )
    {
        bool invalidBox = false;
        mLastCandidate = NULL;
        double relativeContraction = 1;
        double absoluteContraction = 0;
        bool contractionApplied = false;
        for( ; ; )
        {
            #ifndef BOXMANAGEMENT
            while(!mBoxStorage.empty())
                mBoxStorage.pop();

            icp::set_icpVariable icpVariables;
            Variables originalRealVariables;
            rReceivedFormula().realValuedVars(originalRealVariables);
            for( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
            {
                assert(mVariables.count(*variablesIt) > 0);
                icpVariables.insert( (*(mVariables.find(*variablesIt))).second );
            }
            std::set<FormulaT> box = variableReasonHull(icpVariables);
            mBoxStorage.push(box);
//            cout << "ADD TO BOX!" << endl;
            #endif
            #ifdef ICP_MODULE_DEBUG_0
            cout << "********************** [ICP] Contraction **********************" << endl;
            //cout << "Subtree size: " << mHistoryRoot->sizeSubtree() << endl;
            mHistoryActual->print();
            #endif
            #ifdef ICP_BOXLOG
            icpLog << "startContraction";
            writeBox();
            #endif
            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            FormulaT negatedContraction = FormulaT( *mpReceivedFormula );
            GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
            for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                tmp.insert((*constraintIt));

            std::set<FormulaT> boundaryConstraints = createConstraintsFromBounds(tmp);
            for ( auto boundaryConstraint = boundaryConstraints.begin(); boundaryConstraint != boundaryConstraints.end(); ++boundaryConstraint )
                negatedContraction->addSubformula(*boundaryConstraint);
            #endif
            // prepare IcpRelevantCandidates
//            activateLinearEquations(); // TODO (Florian): do something alike again
            fillCandidates();
            _splitOccurred = false;

            while ( !mIcpRelevantCandidates.empty() && !_splitOccurred )
            {
                #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                mCheckContraction = new FormulaT(*mpReceivedFormula);

                GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                    tmp.insert((*constraintIt));

                std::set<FormulaT> boundaryConstraints = createConstraintsFromBounds(tmp);
                for ( auto boundaryConstraint = boundaryConstraints.begin(); boundaryConstraint != boundaryConstraints.end(); ++boundaryConstraint )
                    mCheckContraction->addSubformula(*boundaryConstraint);
                #endif

                icp::ContractionCandidate* candidate = chooseContractionCandidate();
                assert(candidate != NULL);
                relativeContraction = -1;
                absoluteContraction = 0;
                _splitOccurred = contraction( candidate, relativeContraction, absoluteContraction );
                #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                if ( !_splitOccurred && relativeContraction != 0 )
                {
                    GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                    for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                        tmp.insert((*constraintIt));

                    std::set<FormulaT> contractedBox = createConstraintsFromBounds(tmp);
                    FormulaT* negBox = new FormulaT(NOT);
                    FormulaT* boxConjunction = new FormulaT(AND);
                    for ( auto formulaIt = contractedBox.begin(); formulaIt != contractedBox.end(); ++formulaIt )
                        boxConjunction->addSubformula(*formulaIt);

                    negBox->addSubformula(boxConjunction);
                    mCheckContraction->addSubformula(negBox);
                    addAssumptionToCheck(*mCheckContraction,false,"SingleContractionCheck");
                }
                mCheckContraction->clear();
                delete mCheckContraction;
                #endif

                // catch if new interval is empty -> we can drop box and chose next box
                if ( mIntervals.at(candidate->derivationVar()).isEmpty() )
                {
                    #ifdef ICP_MODULE_DEBUG_0
                    cout << "GENERATED EMPTY INTERVAL, Drop Box: " << endl;
                    #endif
                    mLastCandidate = candidate;
                    invalidBox = true;
                    break;
                }

                if ( relativeContraction > 0 )
                {
                    mLastCandidate = candidate;
                    contractionApplied = true;
                }

                // update weight of the candidate
                removeCandidateFromRelevant(candidate);
                candidate->setPayoff(relativeContraction);
                candidate->calcRWA();

                // only add nonlinear CCs as linear CCs should only be used once
                if ( !candidate->isLinear() )
                {
					// TODO: Improve - no need to add irrelevant candidates (see below)
                    addCandidateToRelevant(candidate);
                }

                assert(mIntervals.find(candidate->derivationVar()) != mIntervals.end() );
                #ifdef ICP_CONSIDER_WIDTH
                if ( (relativeContraction < mContractionThreshold && !_splitOccurred) || mIntervals.at(candidate->derivationVar()).diameter() <= mTargetDiameter )
                #else
                if ( (absoluteContraction < mContractionThreshold && !_splitOccurred) )
                #endif
                {
                    removeCandidateFromRelevant(candidate);
                }
                #ifdef ICP_CONSIDER_WIDTH
                else if ( relativeContraction >= mContractionThreshold )
                #else
                else if ( absoluteContraction >= mContractionThreshold )
                #endif
                {
                    /**
                     * make sure all candidates which contain the variable
                     * of which the interval has significantly changed are
                     * contained in mIcpRelevantCandidates.
                     */
                    std::map<carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(candidate->derivationVar());
                    assert(icpVar != mVariables.end());
                    for ( auto candidateIt = (*icpVar).second->candidates().begin(); candidateIt != (*icpVar).second->candidates().end(); ++candidateIt )
                    {
                        bool toAdd = true;
                        for ( auto relevantCandidateIt = mIcpRelevantCandidates.begin(); relevantCandidateIt != mIcpRelevantCandidates.end(); ++relevantCandidateIt )
                        {
                            if ( (*relevantCandidateIt).second == (*candidateIt)->id() )
                                toAdd = false;
                        }
                        #ifdef ICP_CONSIDER_WIDTH
                        if ( toAdd && (*candidateIt)->isActive() && mIntervals.at((*candidateIt)->derivationVar()).diameter() > mTargetDiameter )
                        #else
                        if( toAdd && (*candidateIt)->isActive() )
                        #endif
                        {
                            addCandidateToRelevant(*candidateIt);
                        }
                    }
                    #ifdef ICP_BOXLOG
                    icpLog << "contraction; \n";
                    #endif
                }

                #ifdef ICP_CONSIDER_WIDTH
                bool originalAllFinished = true;
                Variables originalRealVariables;
                rReceivedFormula().realValuedVars(originalRealVariables);
                for( auto varIt = originalRealVariables.begin(); varIt != originalRealVariables.end(); ++varIt )
                {
                    auto varInterval = mIntervals.find(*varIt);
                    if( varInterval != mIntervals.end() )
                    {
                        if( varInterval->second.diameter() > mTargetDiameter )
                        {
                            originalAllFinished = false;
                            break;
                        }
                    }
                }
                if( originalAllFinished )
                {
                    mIcpRelevantCandidates.clear();
                    break;
                }
                #endif
            } //while ( !mIcpRelevantCandidates.empty() && !_splitOccurred)
            // verify if the box is already invalid
            if (!invalidBox && !_splitOccurred)
            {
                invalidBox = !checkBoxAgainstLinearFeasibleRegion();
                #ifdef ICP_MODULE_DEBUG_0
                cout << "Invalid against linear region: " << (invalidBox ? "yes!" : "no!") << endl;
                #endif
                #ifdef ICP_BOXLOG
                if ( invalidBox )
                {
                    icpLog << "invalid Post Contraction; \n";
                }
                #endif
                // do a quick test with one point.
//                if( !invalidBox )
//                {
//                    EvalRationalMap rationals;
//                    std::map<carl::Variable, double> values = createModel();
//                    for(auto value : values)
//                    {
//                        rationals.insert(std::make_pair(value.first, carl::rationalize<Rational>(value.second)));
//                    }
//                    unsigned result = mpReceivedFormula->satisfiedBy(rationals);
//                    if ( result == 1 )
//                    {
//                        return foundAnswer(True);
//                    }
//                }
            }
            #ifdef ICP_BOXLOG
            else
            {
                icpLog << "contract to emp; \n";
            }
            #endif
            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            if ( !_splitOccurred && !invalidBox )
            {
                GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                    tmp.insert((*constraintIt));

                std::set<FormulaT> contractedBox = createConstraintsFromBounds(tmp);
                FormulaT* negConstraint = new FormulaT(NOT);
                FormulaT* conjunction = new FormulaT(AND);
                for ( auto formulaIt = contractedBox.begin(); formulaIt != contractedBox.end(); ++formulaIt )
                    conjunction->addSubformula(*formulaIt);

                negConstraint->addSubformula(conjunction);
                negatedContraction->addSubformula(negConstraint);
                addAssumptionToCheck(*negatedContraction,false,"ICPContractionCheck");
            }
            negatedContraction->clear();
            delete negatedContraction;
            #endif
            if( invalidBox )
                return true;
            if( _splitOccurred || mIcpRelevantCandidates.empty() ) // relevantCandidates is not empty, if we got new bounds from LRA during boxCheck
            {
                // perform splitting if possible
                if( !_splitOccurred )
                {
                    _splitOccurred = checkAndPerformSplit( contractionApplied ) != carl::Variable::NO_VARIABLE;
                }
                if( _splitOccurred )
                {
                    #ifdef ICP_BOXLOG
                    icpLog << "split size subtree; " << mHistoryRoot->sizeSubtree() << "\n";
                    #endif
                    #ifdef ICP_MODULE_DEBUG_1
                    cout << "Size subtree: " << mHistoryActual->sizeSubtree() << " \t Size total: " << mHistoryRoot->sizeSubtree() << endl;
                    #endif
                    #ifdef BOXMANAGEMENT
                    invalidBox = false;
                    #else
                    return invalidBox;
                    #endif
                }
                else
                    return false;

                #ifdef ICP_MODULE_DEBUG_0
                cout << "empty: " << invalidBox << "  _splitOccurred: " << _splitOccurred << endl;
                #endif
            }
        }
        assert( false ); // should not happen
        return invalidBox;
    }
    
    Answer ICPModule::callBackends()
    {
        #ifdef ICP_MODULE_DEBUG_0
        cout << "[ICP] created passed formula." << endl;
        printPassedFormula();
        #endif
        #ifdef ICP_BOXLOG
        icpLog << "backend";
        writeBox();
        #endif
        ++mCountBackendCalls;
        Answer a = runBackends();
        mIsBackendCalled = true;
        #ifdef ICP_MODULE_DEBUG_0
        cout << "[ICP] Done running backends: " << ANSWER_TO_STRING( a ) << endl;
        #endif
        if( a == False )
        {
            assert(infeasibleSubsets().empty());
            #ifndef BOXMANAGEMENT
            std::set<FormulaT> contractionConstraints = this->createPremiseDeductions();
            vector<Module*>::const_iterator backend = usedBackends().begin();
            while( backend != usedBackends().end() )
            {
                assert( !(*backend)->infeasibleSubsets().empty() );
                #ifdef ICP_MODULE_DEBUG_0
                (*backend)->printInfeasibleSubsets();
                #endif
                for( auto infsubset = (*backend)->infeasibleSubsets().begin(); infsubset != (*backend)->infeasibleSubsets().end(); ++infsubset )
                {
                    std::set<FormulaT> newInfSubset;
                    for( auto subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                    {
                        if( !subformula->constraint().isBound() )
                            newInfSubset.insert( newInfSubset.end(), *subformula );
                    }
                    newInfSubset.insert( contractionConstraints.begin(), contractionConstraints.end() );
                    mInfeasibleSubsets.push_back( newInfSubset );
                }
                ++backend;
            }
            return False;
            #else
            bool isBoundInfeasible = false;
            bool isBound = false;

            vector<Module*>::const_iterator backend = usedBackends().begin();
            while( backend != usedBackends().end() )
            {
                assert( !(*backend)->infeasibleSubsets().empty() );
                for( vec_set_const_pFormula::const_iterator infsubset = (*backend)->infeasibleSubsets().begin();
                        infsubset != (*backend)->infeasibleSubsets().end(); ++infsubset )
                {
                    for( auto subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                    {
                        isBound = false;
                        std::map<carl::Variable, icp::IcpVariable*>::iterator iter = mVariables.begin();
                        for ( ; iter != mVariables.end(); ++iter )
                        {
                            icp::IcpVariable& icpVar = *(*iter).second;
                            if( icpVar.isOriginal() )
                            {
                                assert( icpVar.isExternalUpdated() == icp::Updated::NONE );
                                if( (icpVar.externalLeftBound() != mpPassedFormula->end() && *subformula == *icpVar.externalLeftBound())
                                    || (icpVar.externalRightBound() != mpPassedFormula->end() && *subformula == *icpVar.externalRightBound()) )
                                {
                                    isBound = true;
                                    isBoundInfeasible = true;
                                    assert(mVariables.find( *(*subformula)->constraint().variables().begin() ) != mVariables.end() );
                                    mHistoryActual->addInfeasibleVariable( mVariables.at( *(*subformula)->constraint().variables().begin() ) );
                                    break;
                                }
                            }
                        }
                        if(!isBound)
                        {
                            if (mInfeasibleSubsets.empty())
                            {
                                std::set<FormulaT> infeasibleSubset;
                                infeasibleSubset.insert(*subformula);
                                mInfeasibleSubsets.insert(mInfeasibleSubsets.begin(), infeasibleSubset);
                            }
                            else
                                (*mInfeasibleSubsets.begin()).insert(*subformula);
                        }
                    }
                }
                break;
            }
            if ( isBoundInfeasible )
            {
                // set stateInfeasibleSubset
                assert(!mInfeasibleSubsets.empty());
                for (auto infSetIt = (*mInfeasibleSubsets.begin()).begin(); infSetIt != (*mInfeasibleSubsets.begin()).end(); ++infSetIt )
                {
                    if( (*infSetIt)->pConstraint()->isBound() )
                    {
                        assert( mVariables.find( *(*infSetIt)->constraint().variables().begin() ) != mVariables.end() );
//                                        mHistoryActual->addInfeasibleVariable( mVariables.at((*(*infSetIt)->constraint().variables().begin()).first) );
//                                        cout << "Added infeasible Variable." << endl;
                    }
                    else
                    {
                        mHistoryActual->addInfeasibleConstraint((*infSetIt)->pConstraint());
//                                        cout << "Added infeasible Constraint." << endl;
                    }

                }
                // clear infeasible subsets
                mInfeasibleSubsets.clear();
                #ifdef ICP_MODULE_DEBUG_0
                cout << "InfSet of Backend contained bound, Chose new box: " << endl;
                #endif
                if( !chooseBox() )
                    return foundAnswer(False);
            }
            else
            {
                mHistoryActual->propagateStateInfeasibleConstraints();
                mHistoryActual->propagateStateInfeasibleVariables();
                mInfeasibleSubsets.clear();
                mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
                // printInfeasibleSubsets();
                return False;
            }
            #endif
        }
        else // if answer == true or answer == unknown
        {
            mHistoryActual->propagateStateInfeasibleConstraints();
            mHistoryActual->propagateStateInfeasibleVariables();
            #ifdef ICP_MODULE_DEBUG_0
            cout << "Backend: " << ANSWER_TO_STRING( a ) << endl;
            #endif
            return a;
        }
    }
        
    Poly ICPModule::createNonlinearCCs( const ConstraintT* _constraint, const vector<Poly>& _tempMonomes )
    {
        Poly linearizedConstraint = smtrat::ZERO_POLYNOMIAL;
        ContractionCandidates ccs;
        // Create contraction candidate object for every possible derivation variable
        for( auto& monom : _tempMonomes )
        {
            auto iter = mVariableLinearizations.find( monom );
            if( iter == mVariableLinearizations.end() ) // no linearization yet
            {
                // create mLinearzations entry
                Variables variables;
                monom.gatherVariables( variables );
                bool hasRealVar = false;
                for( auto var : variables )
                {
                    if( var.getType() == carl::VariableType::VT_REAL )
                    {
                        hasRealVar = true;
                        break;
                    }
                }
                carl::Variable newVar = hasRealVar ? carl::freshRealVariable() : carl::freshIntegerVariable();
                mVariableLinearizations.insert( std::make_pair( monom, newVar ) );
                mSubstitutions.insert( std::make_pair( newVar, monom ) );
                assert( mVariables.find( newVar ) == mVariables.end() );
                icp::IcpVariable* icpVar = getIcpVariable( newVar, false, NULL );
                mHistoryRoot->addInterval( newVar, smtrat::DoubleInterval::unboundedInterval() );
                #ifdef ICP_MODULE_DEBUG_0
                cout << "New replacement: " << monom << " -> " << mVariableLinearizations.at(monom) << endl;
                #endif

                const Poly rhs = monom - newVar;
                for( auto varIndex = variables.begin(); varIndex != variables.end(); ++varIndex )
                {
                    // create a contraction candidate for each variable in the monomial
                    if( mContractors.find(rhs) == mContractors.end() )
                    {
                        mContractors.insert(std::make_pair(rhs, Contractor<carl::SimpleNewton>(rhs)));
                    }
                    const ConstraintT* tmp = newConstraint<Poly>( rhs, Relation::EQ );
                    icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate( newVar, rhs, tmp, *varIndex, mContractors.at( rhs ), FormulaT( FormulaType::TRUE ) );
                    ccs.insert( ccs.end(), tmpCandidate );
                    tmpCandidate->setNonlinear();
                    auto tmpIcpVar = mVariables.find( newVar );
                    assert( tmpIcpVar != mVariables.end() );
                    tmpIcpVar->second->addCandidate( tmpCandidate );
                }
                // add one candidate for the replacement variable
                const ConstraintT* tmp = newConstraint<Poly>( rhs, Relation::EQ );
                icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate( newVar, rhs, tmp, newVar, mContractors.at( rhs ), FormulaT( FormulaType::TRUE ) );
                tmpCandidate->setNonlinear();
                icpVar->addCandidate( tmpCandidate );
                ccs.insert( ccs.end(), tmpCandidate );
            }
            else // already existing replacement/substitution/linearization
            {
                #ifdef ICP_MODULE_DEBUG_1
                cout << "Existing replacement: " << monom << " -> " << mVariableLinearizations.at(monom) << endl;
                #endif
                auto iterB = mVariables.find( iter->second );
                assert( iterB != mVariables.end() );
                // insert already created CCs into the current list of CCs
                ccs.insert( iterB->second->candidates().begin(), iterB->second->candidates().end() );
            }
        }
        // Construct the linearization
        for( auto monomialIt = _constraint->lhs().begin(); monomialIt != _constraint->lhs().end(); ++monomialIt )
        {
            if( (monomialIt)->monomial() == NULL || (monomialIt)->monomial()->isAtMostLinear() )
            {
                linearizedConstraint += *monomialIt;
            }
            else
            {
                assert( mVariableLinearizations.find(Poly((monomialIt)->monomial())) != mVariableLinearizations.end() );
                linearizedConstraint += (monomialIt)->coeff() * (*mVariableLinearizations.find( Poly((monomialIt)->monomial() ))).second;
            }
        }
        mNonlinearConstraints.insert( pair<const ConstraintT*, ContractionCandidates>( _constraint, ccs ) );
        return linearizedConstraint;
    }
    
    void ICPModule::createLinearCCs( const FormulaT& _constraint, const FormulaT& _origin )
    {
        assert( _constraint.getType() == FormulaType::CONSTRAINT );
        assert( _constraint.constraint().lhs().isLinear() );
        const LRAVariable* slackvariable = mLRA.getSlackVariable( _constraint );
        assert( slackvariable != NULL );
        if( mLinearConstraints.find( slackvariable ) == mLinearConstraints.end() )
        {
            Variables variables = _constraint.constraint().variables();
            bool hasRealVar = false;
            for( carl::Variable::Arg var : variables )
            {
                if( var.getType() == carl::VariableType::VT_REAL )
                {
                    hasRealVar = true;
                    break;
                }
            }
            carl::Variable newVar = hasRealVar ? carl::freshRealVariable() : carl::freshIntegerVariable();
            variables.insert( newVar );
            mSubstitutions.insert( std::make_pair( newVar, Poly( newVar ) ) );
            assert( mVariables.find( newVar ) == mVariables.end() );
            icp::IcpVariable* icpVar = getIcpVariable( newVar, false, slackvariable );
            mHistoryRoot->addInterval( newVar, smtrat::DoubleInterval::unboundedInterval() );

            const Poly rhs = slackvariable->expression() - newVar;
            const ConstraintT* tmpConstr = newConstraint<Poly>( rhs, Relation::EQ );
            auto iter = mContractors.find( rhs );
            if( iter == mContractors.end() )
            {
                iter = mContractors.insert( std::make_pair( rhs, Contractor<carl::SimpleNewton>(rhs) ) ).first;
            }

            // Create candidates for every possible variable:
            for( auto var = variables.begin(); var != variables.end(); ++var )
            {   
                icp::ContractionCandidate* newCandidate = mCandidateManager->getInstance()->createCandidate( newVar, rhs, tmpConstr, *var, iter->second, _origin );

                // ensure that the created candidate is set as linear
                newCandidate->setLinear();
                #ifdef ICP_MODULE_DEBUG_1
                cout << "[ICP] Create & activate candidate: ";
                newCandidate->print();
                slackvariable->print();
                #endif
                icpVar->addCandidate( newCandidate );
            }
            mLinearConstraints.insert( pair<const LRAVariable*, ContractionCandidates>( slackvariable, icpVar->candidates() ) );
        }
    }
    
    void ICPModule::initiateWeights()
    {
//        std::map<const Constraint*, ContractionCandidates>::iterator constrIt;
//        ContractionCandidates::iterator   varIt;
//        double                   minDiameter = 0;
//        double maxDiameter = 0;
//        bool                     minSet = false;
//        bool                     maxSet = false;
//        vector<carl::Variable>           variables = vector<carl::Variable>();
//
//        // calculate Jacobian for initial box
//        for( constrIt = mNonlinearConstraints.begin(); constrIt != mNonlinearConstraints.end(); constrIt++ )
//        {
//            std::set<icp::ContractionCandidate*> tmp = constrIt->second;
//
//            minSet = false;
//            maxSet = false;
//
//            for( varIt = tmp.begin(); varIt != tmp.end(); varIt++ )
//            {
//                (*varIt)->calcDerivative();
//
//                variables.clear();
//                const Polynomial term = (*varIt)->derivative();
//                mIcp.searchVariables( term, &variables );
//
//                if( !minSet )
//                {
//                    minDiameter = mIntervals[(*varIt)->derivationVar()].upper() - mIntervals[(*varIt)->derivationVar()].upper();
//                }
//                else
//                {
//                    minDiameter = mIntervals[(*varIt)->derivationVar()].upper() - mIntervals[(*varIt)->derivationVar()].upper() < minDiameter
//                                  ? mIntervals[(*varIt)->derivationVar()].upper() - mIntervals[(*varIt)->derivationVar()].upper() : minDiameter;
//                }
//
//                if( !maxSet )
//                {
//                    maxDiameter = mIntervals[(*varIt)->derivationVar()].upper() - mIntervals[(*varIt)->derivationVar()].upper();
//                }
//                else
//                {
//                    maxDiameter = mIntervals[(*varIt)->derivationVar()].upper() - mIntervals[(*varIt)->derivationVar()].upper() > maxDiameter
//                                  ? mIntervals[(*varIt)->derivationVar()].upper() - mIntervals[(*varIt)->derivationVar()].upper() : maxDiameter;
//                }
//            }
//        }
    }
    
//    void ICPModule::activateLinearEquations()
//    {
//        for( auto candidatesIt = mLinearConstraints.begin(); candidatesIt != mLinearConstraints.end(); ++candidatesIt )
//        {
//            ContractionCandidates candidates = (*candidatesIt).second;
//            for( auto ccIt = candidates.begin(); ccIt != candidates.end(); ++ccIt )
//            {
//                if( (*ccIt)->constraint()->relation() == Relation::EQ )
//                {
//                    (*ccIt)->activate();
//                }
//            }
//        }
//    }
    
    void ICPModule::fillCandidates()
    {
        // fill mIcpRelevantCandidates with the nonlinear contractionCandidates
        for ( icp::ContractionCandidate* nonlinearIt : mActiveNonlinearConstraints )
        {
            // check that assertions have been processed properly
            assert( (*nonlinearIt).activity() == (*nonlinearIt).origin().size() );
            auto varInterval = mIntervals.find((*nonlinearIt).derivationVar());
            assert( varInterval != mIntervals.end() );
#ifdef ICP_CONSIDER_WIDTH
            if ( varInterval->second.diameter() > mTargetDiameter || varInterval->second.diameter() == -1 )
#else
            if ( varInterval->second.diameter() > 0 || varInterval->second.diameter() == -1 )
#endif
            {
                // only add if not already existing
                addCandidateToRelevant( nonlinearIt );
            }
            else // the candidate is not relevant -> delete from icpRelevantCandidates
            {
                removeCandidateFromRelevant(nonlinearIt);
            }
        }
        // fill mIcpRelevantCandidates with the active linear contractionCandidates
        for ( icp::ContractionCandidate* linearIt : mActiveLinearConstraints )
        {
            // check that assertions have been processed properly
            assert( (*linearIt).activity() == (*linearIt).origin().size() );
            auto varInterval = mIntervals.find((*linearIt).derivationVar());
            assert( varInterval != mIntervals.end() );
#ifdef ICP_CONSIDER_WIDTH
            if ( (*linearIt).isActive() && ( varInterval->second.diameter() > mTargetDiameter || varInterval->second.diameter() == -1 ) )
#else
            if ( (*linearIt).isActive() && ( varInterval->second.diameter() > 0 || varInterval->second.diameter() == -1 ) )
#endif
            {
                addCandidateToRelevant( linearIt );
            }
            else // the candidate is not relevant -> delete from icpRelevantCandidates
            {
                removeCandidateFromRelevant( linearIt );
            }
        }
    }
    
    bool ICPModule::addCandidateToRelevant(icp::ContractionCandidate* _candidate)
    {
        if ( _candidate->isActive() )
        {
            mIcpRelevantCandidates.erase( std::pair<double, unsigned>( _candidate->lastRWA(), _candidate->id() ) );
            std::pair<double, unsigned> target(_candidate->RWA(), _candidate->id());
            if ( mIcpRelevantCandidates.find(target) == mIcpRelevantCandidates.end() )
            {
                #ifdef ICP_MODULE_DEBUG_0
                cout << "add to relevant candidates: " << (*_candidate).rhs() << endl;
                cout << "   id: " << (*_candidate).id() << endl;
                cout << "   key: (" << target.first << ", " << target.second << ")" << endl;
                #endif
                mIcpRelevantCandidates.insert(target);
                _candidate->updateLastRWA();
                return true;
            }
        }
        return false;
    }
    
    bool ICPModule::removeCandidateFromRelevant(icp::ContractionCandidate* _candidate)
    {
        std::pair<double, unsigned> target(_candidate->lastRWA(), _candidate->id());
        auto iter = mIcpRelevantCandidates.find( target );
        if( iter != mIcpRelevantCandidates.end() )
        {
            #ifdef ICP_MODULE_DEBUG_0
            cout << "remove from relevant candidates: " << (*_candidate).rhs() << endl;
            cout << "   id: " << (*_candidate).id() << " , Diameter: " << mIntervals[(*_candidate).derivationVar()].diameter() << endl;
            #endif
            mIcpRelevantCandidates.erase(iter);
            return true;
        }
        return false;
    }
    				
    void ICPModule::updateRelevantCandidates(carl::Variable _var, double _relativeContraction)
    {
        // update all candidates which contract in the dimension in which the split has happened
        std::set<icp::ContractionCandidate*> updatedCandidates;
        // iterate over all affected constraints
        std::map<carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(_var);
        assert(icpVar != mVariables.end());
        for ( auto candidatesIt = (*icpVar).second->candidates().begin(); candidatesIt != (*icpVar).second->candidates().end(); ++candidatesIt)
        {
            if ( (*candidatesIt)->isActive() )
            {
                unsigned id = (*candidatesIt)->id();
                // search if candidate is already contained - erase if, else do nothing
                removeCandidateFromRelevant(*candidatesIt);

                // create new tuple for mIcpRelevantCandidates
                mCandidateManager->getInstance()->getCandidate(id)->setPayoff(_relativeContraction );
                mCandidateManager->getInstance()->getCandidate(id)->calcRWA();
                updatedCandidates.insert(*candidatesIt);
            }
        }
        // re-insert tuples into icpRelevantCandidates
        for ( auto candidatesIt = updatedCandidates.begin(); candidatesIt != updatedCandidates.end(); ++candidatesIt )
        {
            #ifdef ICP_CONSIDER_WIDTH
            if ( mIntervals.at(_var).diameter() > mTargetDiameter )
            #endif
            {
                addCandidateToRelevant(*candidatesIt);
            }
        }
    }
    
    icp::ContractionCandidate* ICPModule::chooseContractionCandidate()
    {
        assert(!mIcpRelevantCandidates.empty());
        // as the map is sorted ascending, we can simply pick the last value
        for( auto candidateIt = mIcpRelevantCandidates.rbegin(); candidateIt != mIcpRelevantCandidates.rend(); ++candidateIt )
        {
            icp::ContractionCandidate* cc = mCandidateManager->getInstance()->getCandidate((*candidateIt).second);
            assert( cc != NULL );
            if( cc->isActive() )//&& mIntervals[mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->derivationVar()].diameter() != 0 )
            {
				cc->calcDerivative();
                #ifdef ICP_MODULE_DEBUG_0
                cout << "Choose Candidate: ";
                cc->print();
                cout << endl;
                #endif
                return cc;
            }
        }
        return NULL;
    }
    
    bool ICPModule::contraction( icp::ContractionCandidate* _selection, double& _relativeContraction, double& _absoluteContraction )
    {
        smtrat::DoubleInterval resultA = smtrat::DoubleInterval();
        smtrat::DoubleInterval resultB = smtrat::DoubleInterval();
        bool                   splitOccurred = false;

        // check if derivative is already calculated
        if(_selection->derivative().isZero())
            _selection->calcDerivative();

        const Poly               constr     = _selection->rhs();
        const Poly               derivative = _selection->derivative();
        carl::Variable           variable   = _selection->derivationVar();
        assert( mVariables.find( variable ) != mVariables.end() );
        icp::IcpVariable& icpVar = *mVariables.find( variable )->second;
        const DoubleInterval& icpVarInterval = icpVar.interval();
        bool originalUnbounded = ( icpVarInterval.lowerBoundType() == carl::BoundType::INFTY || icpVarInterval.upperBoundType() == carl::BoundType::INFTY );
        double originalDiameter = icpVarInterval.diameter();
        
        splitOccurred    = _selection->contract( mIntervals, resultA, resultB );
        if( splitOccurred )
        {
            #ifdef ICP_MODULE_DEBUG_0
            #ifdef ICP_MODULE_DEBUG_1   
            cout << "Split occured: " << resultB << " and " << resultA << endl;
            #else
            cout << "Split occured" << endl;
            #endif
            #endif
            smtrat::icp::set_icpVariable variables;
            for( auto variableIt = _selection->constraint()->variables().begin(); variableIt != _selection->constraint()->variables().end(); ++variableIt )
            {
                assert(mVariables.find(*variableIt) != mVariables.end());
                variables.insert(mVariables.at(*variableIt));
            }
            mHistoryActual->addContraction(_selection, variables);
#ifdef BOXMANAGEMENT
            // set intervals and update historytree
            EvalDoubleIntervalMap tmpRight;
            for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                    tmpRight.insert(std::pair<carl::Variable,smtrat::DoubleInterval>(variable, resultA ));
                else
                    tmpRight.insert((*intervalIt));
            }

            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            std::set<FormulaT> partialBox = createConstraintsFromBounds(tmpRight);
            FormulaT* negBox = new FormulaT(NOT);
            FormulaT* boxConjunction = new FormulaT(AND);
            for ( auto formulaIt = partialBox.begin(); formulaIt != partialBox.end(); ++formulaIt )
                boxConjunction->addSubformula(*formulaIt);
            
            negBox->addSubformula(boxConjunction);
            mCheckContraction->addSubformula(negBox);
            partialBox.clear();
            #endif

            icp::HistoryNode* newRightChild = new icp::HistoryNode(tmpRight, mCurrentId+2);
            newRightChild->setSplit( icp::intervalToConstraint( variable,tmpRight.at(variable) ).first );
            mHistoryActual->addRight(newRightChild);
            #ifdef ICP_MODULE_DEBUG_1
            cout << "Created node:" << endl;
            newRightChild->print();
            #endif
            
            // left first!
            EvalDoubleIntervalMap tmpLeft = EvalDoubleIntervalMap();
            for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                    tmpLeft.insert(std::pair<carl::Variable,smtrat::DoubleInterval>(variable, resultB ));
                else
                    tmpLeft.insert((*intervalIt));
            }
            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            partialBox = createConstraintsFromBounds(tmpLeft);
            FormulaT* negBox2 = new FormulaT(NOT);
            FormulaT* boxConjunction2 = new FormulaT(AND);
            for ( auto formulaIt = partialBox.begin(); formulaIt != partialBox.end(); ++formulaIt )
                boxConjunction2->addSubformula(*formulaIt);
            
            negBox2->addSubformula(boxConjunction2);
            mCheckContraction->addSubformula(negBox2);
            addAssumptionToCheck(*mCheckContraction,false,"SplitCheck");
            mCheckContraction->clear();
            #endif
            icp::HistoryNode* newLeftChild = new icp::HistoryNode(tmpLeft,++mCurrentId);
            newLeftChild->setSplit( icp::intervalToConstraint( variable, tmpLeft.at(variable) ).second );
            ++mCurrentId;
            mHistoryActual = mHistoryActual->addLeft(newLeftChild);
            #ifdef ICP_MODULE_DEBUG_1   
            cout << "Created node:" << endl;
            newLeftChild->print();
            #endif
            // update mIntervals - usually this happens when changing to a different box, but in this case it has to be done manually, otherwise mIntervals is not affected.
            mIntervals[variable] = resultB;
#else
            /// create prequesites: ((oldBox AND CCs) -> newBox) in CNF: (oldBox OR CCs) OR newBox 
            std::set<FormulaT> subformulas;
            std::set<FormulaT> splitPremise = createPremiseDeductions();
            for( const FormulaT& subformula : splitPremise )
                subformulas.insert( FormulaT( FormulaType::NOT, subformula ) );
            // construct new box
            std::set<FormulaT> boxFormulas = createBoxFormula();
            // push deduction
            if( boxFormulas.size() > 1 )
            {
                auto lastFormula = --boxFormulas.end();
                for( auto iter = boxFormulas.begin(); iter != lastFormula; ++iter )
                {
                    std::set<FormulaT> subformulasTmp = subformulas;
                    subformulasTmp.insert( *iter );
                    addDeduction( FormulaT( OR, subformulas ) );
                }
            }

            // create split: (not h_b OR (Not x<b AND x>=b) OR (x<b AND Not x>=b) )
            assert(resultA.upperBoundType() != BoundType::INFTY );
            Rational bound = carl::rationalize<Rational>( resultA.upper() );
            if( probablyLooping( Poly( variable ), bound ) )
            {
                cout << "probably looping!" << endl;
                Module::storeAssumptionsToCheck( *mpManager );
                exit( 7771 );
            }
            //assert( !probablyLooping( Polynomial( variable ), bound ) );
            Module::branchAt( Poly( variable ), bound, splitPremise, true );
            #ifdef ICP_MODULE_DEBUG_0
            cout << "division causes split on " << variable << " at " << bound << "!" << endl << endl;
            #endif
#endif
            // TODO: Shouldn't it be the average of both contractions?
            _relativeContraction = (originalDiameter - resultB.diameter()) / originalDiameter;
            _absoluteContraction = originalDiameter - resultB.diameter();
        }
        else
        {
            // set intervals
            icpVar.setInterval( resultA );
            #ifdef ICP_MODULE_DEBUG_0
            cout << "      New interval: " << variable << " = " << mIntervals.at(variable) << endl;
            #endif
            if ( icpVarInterval.upperBoundType() != carl::BoundType::INFTY && icpVarInterval.lowerBoundType() != carl::BoundType::INFTY && !originalUnbounded )
            {
                if ( originalDiameter == 0 )
                {
                    _relativeContraction = 0;
                    _absoluteContraction = 0;
                }
                else
                {
                    _relativeContraction = 1 - (icpVarInterval.diameter() / originalDiameter);
                    _absoluteContraction = originalDiameter - icpVarInterval.diameter();
                }
            }
            else if ( originalUnbounded && icpVarInterval.isUnbounded() == false ) // if we came from infinity and got a result, we achieve maximal relative contraction
            {
                _relativeContraction = 1;
                _absoluteContraction = std::numeric_limits<double>::infinity();
            }
            
            if (_relativeContraction > 0)
            {
                mHistoryActual->addInterval(_selection->lhs(), mIntervals.at(_selection->lhs()));
                smtrat::icp::set_icpVariable variables;
                for( auto variableIt = _selection->constraint()->variables().begin(); variableIt != _selection->constraint()->variables().end(); ++variableIt )
                {
                    assert(mVariables.find(*variableIt) != mVariables.end());
                    variables.insert(mVariables.at(*variableIt));
                }
                mHistoryActual->addContraction(_selection, variables);
            }
            
            #ifdef ICP_MODULE_DEBUG_0
            cout << "      Relative contraction: " << _relativeContraction << endl;
            #endif
        }
        return splitOccurred;
    }
    
    std::map<carl::Variable, double> ICPModule::createModel( bool antipoint ) const
    {
        // Note that we do not need to consider INFTY bounds in the calculation of the antipoint.
        std::map<carl::Variable, double> assignments;
        auto varIntervalIt = mIntervals.begin();
        for( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
        {
            assert( varIntervalIt->first == varIt->first );
            assert( varIt->second->var() == varIt->first );
            double value = 0;
            if( !varIntervalIt->second.isUnbounded() )
            {
                bool takeLower = false;
                bool takeUpper = false;
                if( antipoint ) // Find a point within the interval bounds which is most likely NOT SATISFYING all constraints
                {
                    switch( (*varIt).second->isInternalUpdated() )
                    {
                        case icp::Updated::BOTH:
                            takeLower = true;
                            break;
                        case icp::Updated::LEFT:
                            takeLower = true;
                            break;
                        case icp::Updated::RIGHT:
                            takeUpper = true;
                            break;
                        default:
                            takeLower = true;
                            takeUpper = true;
                    }
                }
                else // Find a point within the interval which is most likely SATISFYING all constraints
                {
                    switch( (*varIt).second->isInternalUpdated() )
                    {
                        case icp::Updated::BOTH:
                            takeLower = true;
                            takeUpper = true;
                            break;
                        case icp::Updated::LEFT:
                            takeUpper = true;
                            break;
                        case icp::Updated::RIGHT:
                            takeLower = true;
                            break;
                        default:
                            takeLower = true;
                    }
                }
                if( takeLower && takeUpper )
                {
                    if(varIntervalIt->second.isPointInterval())
                            value = varIntervalIt->second.lower();
                    else
                            value = varIntervalIt->second.sample(false);
                }
                else if( takeLower )
                {
                    if( varIntervalIt->second.lowerBoundType() == BoundType::INFTY )
                    {
                        value = varIntervalIt->second.upperBoundType() == BoundType::WEAK ? varIntervalIt->second.upper() : std::nextafter( varIntervalIt->second.upper(), -INFINITY );
                    }
                    else
                    {
                        value = varIntervalIt->second.lowerBoundType() == BoundType::WEAK ? varIntervalIt->second.lower() : std::nextafter( varIntervalIt->second.lower(), INFINITY );
                    }
                }
                else
                {   
                    if( varIntervalIt->second.upperBoundType() == BoundType::INFTY )
                    {
                        value = varIntervalIt->second.lowerBoundType() == BoundType::WEAK ? varIntervalIt->second.lower() : std::nextafter( varIntervalIt->second.lower(), INFINITY );
                    }
                    else
                    {
                        value = varIntervalIt->second.upperBoundType() == BoundType::WEAK ? varIntervalIt->second.upper() : std::nextafter( varIntervalIt->second.upper(), -INFINITY );
                    }
                }
            }
            assert( varIntervalIt->second.contains( value ));
            assignments.insert( std::make_pair(varIt->first, value) );
            ++varIntervalIt;
        }
        return assignments;
    }
    
    void ICPModule::updateModel() const
    {
        clearModel();
        if( solverState() == True )
        {
            if( mFoundSolution.empty() )
            {
                Module::getBackendsModel();
                EvalRationalMap rationalAssignment = mLRA.getRationalModel();
                for( auto assignmentIt = rationalAssignment.begin(); assignmentIt != rationalAssignment.end(); ++assignmentIt )
                {
                    auto varIt = mVariables.find((*assignmentIt).first);
                    if(  varIt != mVariables.end() && (*varIt).second->isOriginal() )
                    {
                        Poly value = Poly( assignmentIt->second );
                        ModelValue assignment = vs::SqrtEx(value);
                        mModel.insert(std::make_pair(assignmentIt->first, assignment));
                    }
                }
            }
            else
            {   
                for( auto assignmentIt = mFoundSolution.begin(); assignmentIt != mFoundSolution.end(); ++assignmentIt )
                {
                    auto varIt = mVariables.find((*assignmentIt).first);
                    if(  varIt != mVariables.end() && (*varIt).second->isOriginal() )
                    {
                        Poly value = Poly( assignmentIt->second );
                        ModelValue assignment = vs::SqrtEx(value);
                        mModel.insert( std::make_pair( assignmentIt->first, assignment ) );
                    }
                }
            }
        }
    }
    
    ModuleInput::iterator ICPModule::eraseSubformulaFromPassedFormula( ModuleInput::iterator _subformula, bool _ignoreOrigins )
    {
        for( std::map<carl::Variable, icp::IcpVariable*>::iterator iter = mVariables.begin(); iter != mVariables.end(); ++iter )
        {
            icp::IcpVariable& icpVar = *iter->second;
            assert( icpVar.externalLeftBound() == passedFormulaEnd() || icpVar.externalLeftBound() != icpVar.externalRightBound() );
            if( icpVar.externalLeftBound() == _subformula )
            {
                icpVar.setExternalLeftBound( passedFormulaEnd() );
                break;
            }
            else if( icpVar.externalRightBound() == _subformula )
            {
                icpVar.setExternalRightBound( passedFormulaEnd() );
                break;
            }
        }
        auto res = Module::eraseSubformulaFromPassedFormula( _subformula, _ignoreOrigins );
        return res;
    }
    
    void ICPModule::tryContraction( icp::ContractionCandidate* _selection, double& _relativeContraction, const EvalDoubleIntervalMap& _intervals )
    {
        EvalDoubleIntervalMap intervals = _intervals;
        smtrat::DoubleInterval resultA = smtrat::DoubleInterval();
        smtrat::DoubleInterval resultB = smtrat::DoubleInterval();
        bool splitOccurred = false;

        // check if derivative is already calculated
        if(_selection->derivative().isZero())
            _selection->calcDerivative();

        const Poly               constr     = _selection->rhs();
        const Poly               derivative = _selection->derivative();
        carl::Variable           variable   = _selection->derivationVar();
        assert(intervals.find(variable) != intervals.end());
        double                 originalDiameter = intervals.at(variable).diameter();
        bool originalUnbounded = ( intervals.at(variable).lowerBoundType() == carl::BoundType::INFTY || intervals.at(variable).upperBoundType() == carl::BoundType::INFTY );
        
//        splitOccurred = mIcp.contract<GiNaCRA::SimpleNewton>( intervals, constr, derivative, variable, resultA, resultB );
        splitOccurred    = _selection->contract( mIntervals, resultA, resultB );
        
        if( splitOccurred )
        {
            smtrat::DoubleInterval originalInterval = intervals.at(variable);
            
            EvalDoubleIntervalMap tmpRight = EvalDoubleIntervalMap();
            for ( auto intervalIt = intervals.begin(); intervalIt != intervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                    tmpRight.insert(std::pair<carl::Variable,smtrat::DoubleInterval>(variable, resultA ));
                else
                    tmpRight.insert((*intervalIt));
            }
            
            // left first!
            EvalDoubleIntervalMap tmpLeft = EvalDoubleIntervalMap();
            for ( auto intervalIt = intervals.begin(); intervalIt != intervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                    tmpLeft.insert(std::pair<carl::Variable,smtrat::DoubleInterval>(variable, resultB ));
                else
                    tmpLeft.insert((*intervalIt));
            }
            _relativeContraction = (originalDiameter - resultB.diameter()) / originalInterval.diameter();
        }
        else
        {
            // set intervals
            intervals[variable] = resultA;
            if ( intervals.at(variable).upperBoundType() != carl::BoundType::INFTY && intervals.at(variable).lowerBoundType() != carl::BoundType::INFTY && !originalUnbounded )
            {
                if ( originalDiameter == 0 )
                    _relativeContraction = 0;
                else
                    _relativeContraction = 1 - (intervals.at(variable).diameter() / originalDiameter);
            }
            else if ( originalUnbounded && intervals.at(variable).isUnbounded() == false ) // if we came from infinity and got a result, we achieve maximal relative contraction
                _relativeContraction = 1;
        }
    }
    
    double ICPModule::calculateSplittingImpact ( carl::Variable::Arg _var, icp::ContractionCandidate& _candidate ) const
    {
        double impact = 0;
        assert(mIntervals.count(_var) > 0);
        //assert(_var == _candidate.derivationVar()); // must be uncommented in order to be compilable with clang++
        double originalDiameter = mIntervals.at(_var).diameter();
        switch(mSplittingStrategy)
        {
            case 1: // Select biggest interval
            {
                impact = originalDiameter;
                break;
            }
            case 2: // Rule of Hansen and Walster - select interval with most varying function values
            {
                EvalDoubleIntervalMap* tmpIntervals = new EvalDoubleIntervalMap(mIntervals);
                tmpIntervals->insert(std::make_pair(_var,smtrat::DoubleInterval(1)));
                smtrat::DoubleInterval derivedEvalInterval = carl::IntervalEvaluation::evaluate(_candidate.derivative(), *tmpIntervals);
                impact = derivedEvalInterval.diameter() * originalDiameter;
                delete tmpIntervals;
                break;
            }
            case 3: // Rule of Ratz - minimize width of inclusion
            {
                EvalDoubleIntervalMap* tmpIntervals = new EvalDoubleIntervalMap(mIntervals);
                tmpIntervals->insert(std::make_pair(_var,smtrat::DoubleInterval(1)));
                smtrat::DoubleInterval derivedEvalInterval = carl::IntervalEvaluation::evaluate(_candidate.derivative(), *tmpIntervals);
                smtrat::DoubleInterval negCenter = smtrat::DoubleInterval(mIntervals.at(_var).sample()).inverse();
                negCenter = negCenter.add(mIntervals.at(_var));
                derivedEvalInterval = derivedEvalInterval.mul(negCenter);
                impact = derivedEvalInterval.diameter();
                delete tmpIntervals;
                break;
            }
            case 4: // Select according to optimal machine representation of bounds
            {
                if(mIntervals.at(_var).contains(0))
                {
                    impact = originalDiameter;
                }
                else
                {
                    impact = originalDiameter/(mIntervals.at(_var).upper() > 0 ? mIntervals.at(_var).lower() : mIntervals.at(_var).upper());
                }
                break;
            }
            default:
            {
                impact = originalDiameter;
                break;
            }
        }
        #ifdef ICP_MODULE_DEBUG_0
        cout << __PRETTY_FUNCTION__ << " Rule " << mSplittingStrategy << ": " << impact << endl;
        #endif
        return impact;
    }

    std::set<FormulaT> ICPModule::createPremiseDeductions()
    {
        // collect applied contractions
        std::set<FormulaT> contractions = mHistoryActual->appliedConstraints();
        // collect original box
//        assert( mBoxStorage.size() == 1 );
        std::set<FormulaT> box = mBoxStorage.front();
        contractions.insert( box.begin(), box.end() );
        mBoxStorage.pop();
        return contractions;
    }
    
    std::set<FormulaT> ICPModule::createBoxFormula()
    {
        Variables originalRealVariables;
        rReceivedFormula().realValuedVars(originalRealVariables);
        std::set<FormulaT> subformulas;
        for( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
        {
            if( originalRealVariables.find( (*intervalIt).first ) != originalRealVariables.end() )
            {
                std::pair<const ConstraintT*, const ConstraintT*> boundaries = icp::intervalToConstraint((*intervalIt).first, (*intervalIt).second);
                if(boundaries.first != NULL)
                {
                    subformulas.insert( FormulaT( boundaries.first ) );                       
                }
                if(boundaries.second != NULL)
                {
                    subformulas.insert( FormulaT( boundaries.second ) );
                }
            }
        }
        return subformulas;
    }
    
    carl::Variable ICPModule::checkAndPerformSplit( bool _contractionApplied )
    {
        carl::Variable variable = carl::Variable::NO_VARIABLE; // Initialized to some dummy value
        double maximalImpact = 0;
        bool found = false;
        // first check all intervals from nonlinear contractionCandidates -> backwards to begin at the most important candidate
        // TODO: Why running over the ccs?? You are searching for an original variable whose interval is bigger than target and having a big splitting impact.
        //       For some reason the splitting impact needs the cc to be calculated, why? My suggestion: run over mVariables somehow and don't stop if the 
        //       first suitable variable is found. Maybe there must be stored something to be able to run over mVariables.
        for( auto candidateIt = mActiveNonlinearConstraints.rbegin(); candidateIt != mActiveNonlinearConstraints.rend(); ++candidateIt )
        {
            if( found )
                break;
            variable = *(*candidateIt)->constraint()->variables().begin();
            // search for the biggest interval and check if it is larger than the target Diameter
            for ( auto variableIt = (*candidateIt)->constraint()->variables().begin(); variableIt != (*candidateIt)->constraint()->variables().end(); ++variableIt )
            {
                if( mVariables.find(*variableIt)->second->isOriginal() )
                {
                    auto varInterval = mIntervals.find(*variableIt);
                    if( varInterval != mIntervals.end() && varInterval->second.diameter() > mTargetDiameter )
                    {
                        if(mSplittingStrategy > 0)
                        {
                            double actualImpact = calculateSplittingImpact(*variableIt, **candidateIt);
                            if( actualImpact > maximalImpact )
                            {
                                variable = *variableIt;
                                found = true;
                                maximalImpact = actualImpact;
                            }
                        }
                        else
                        {
                            variable = *variableIt;
                            found = true;
                            break;
                        }
                    }
                }
            }
        }
        for( auto candidateIt = mActiveLinearConstraints.rbegin(); candidateIt != mActiveLinearConstraints.rend(); ++candidateIt )
        {
            if( found )
                break;
            variable = *(*candidateIt)->constraint()->variables().begin();
            // search for the biggest interval and check if it is larger than the target Diameter
            for( auto variableIt = (*candidateIt)->constraint()->variables().begin(); variableIt != (*candidateIt)->constraint()->variables().end(); ++variableIt )
            {
                std::map<carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
                assert(icpVar != mVariables.end());
                if( mVariables.find(*variableIt)->second->isOriginal() )
                {
                    auto varInterval = mIntervals.find(*variableIt);
                    if( varInterval != mIntervals.end() && varInterval->second.diameter() > mTargetDiameter )
                    {
                        if(mSplittingStrategy > 0)
                        {
                            double actualImpact = calculateSplittingImpact(*variableIt, **candidateIt);
                            if( actualImpact > maximalImpact )
                            {
                                variable = *variableIt;
                                found = true;
                                maximalImpact = actualImpact;
                            }
                        }
                        else
                        {
                            variable = *variableIt;
                            found = true;
                            break;
                        }
                    }
                }
            }
        }
        if( found )
        {
            #ifndef BOXMANAGEMENT
            // create prequesites: ((oldBox AND CCs) -> newBox) in CNF: (oldBox OR CCs) OR newBox 
            std::set<FormulaT> splitPremise = createPremiseDeductions();
            if( _contractionApplied )
            {
                std::set<FormulaT> subformulas;
                for( auto formulaIt = splitPremise.begin(); formulaIt != splitPremise.end(); ++formulaIt )
                    subformulas.insert( FormulaT( FormulaType::NOT, *formulaIt ) );
                // construct new box
                subformulas.insert( FormulaT( AND, std::move( createBoxFormula() ) ) ); // TODO: only add this deduction if any contraction took place!!!
                // push deduction
                addDeduction( FormulaT( OR, subformulas ) );
            }
            
            // create split: (not h_b OR (Not x<b AND x>=b) OR (x<b AND Not x>=b) )
            Rational bound = carl::rationalize<Rational>( mIntervals.at(variable).sample( false ) );
            
            if( probablyLooping( Poly( variable ), bound ) )
            {
                cout << "probably looping!" << endl;
                Module::storeAssumptionsToCheck( *mpManager );
                exit( 7771 );
            }
            //assert( !probablyLooping( Polynomial( variable ), bound ) );
            Module::branchAt( Poly( variable ), bound, splitPremise, false );
            #ifdef ICP_MODULE_DEBUG_0
            cout << "force split on " << variable << " at " << bound << "!" << endl << endl;
            #endif
            return variable;
            #else
            //perform split and add two historyNodes
            #ifdef ICP_MODULE_DEBUG_0
            cout << "[ICP] Split performed in: " << variable<< endl;
            cout << "Size mIntervals: " << mIntervals.size() << endl;
            #endif
            // set intervals and update historytree
            DoubleInterval tmp = mIntervals.at(variable);
            DoubleInterval tmpRightInt = tmp;
            tmpRightInt.cutUntil(tmp.sample());
            tmpRightInt.setLeftType(BoundType::WEAK);
            mIntervals[variable] = tmpRightInt;
            EvalDoubleIntervalMap tmpRight;

            for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                tmpRight.insert((*constraintIt));

            icp::HistoryNode* newRightChild = new icp::HistoryNode(tmpRight, mCurrentId+2);
            std::pair<const ConstraintT*, const ConstraintT*> boundaryConstraints = icp::intervalToConstraint(variable, tmpRightInt);
            newRightChild->setSplit(boundaryConstraints.first);
            mHistoryActual->addRight(newRightChild);

            // left first!
            DoubleInterval tmpLeftInt = tmp;
            tmpLeftInt.cutFrom(tmp.sample());
            tmpLeftInt.setRightType(BoundType::STRICT);
            EvalDoubleIntervalMap tmpLeft;

            for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                tmpLeft.insert((*constraintIt));

            icp::HistoryNode* newLeftChild = new icp::HistoryNode(tmpLeft, ++mCurrentId);
            boundaryConstraints = icp::intervalToConstraint(variable, tmpLeftInt);
            newLeftChild->setSplit(boundaryConstraints.second);
            ++mCurrentId;
            mHistoryActual = mHistoryActual->addLeft(newLeftChild);
            updateRelevantCandidates(variable, 0.5 );
            // only perform one split at a time and then contract
            result = variable;
            std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(variable.get_name());
            assert(icpVar != mVariables.end());
            icpVar->second->setInterval( tmpLeftInt );
            return result;
            #endif
        }
        return carl::Variable::NO_VARIABLE;
    }
    
    bool ICPModule::tryTestPoints()
    {
        bool testSuccessful = true;
        // find a point within the intervals
        std::map<carl::Variable, double> antipoint = createModel( true );
        mFoundSolution.clear();
        #ifdef ICP_MODULE_DEBUG_0
        cout << "Try test point:" << endl;
        #endif
        for( auto iter = antipoint.begin(); iter != antipoint.end(); ++iter )
        {
            #ifdef ICP_MODULE_DEBUG_0
            cout << "    " << iter->first << " -> " << std::setprecision(20) << iter->second << "  which is the rational " << carl::rationalize<Rational>( iter->second )  << endl;
            #endif
            mFoundSolution.insert( std::make_pair( iter->first, carl::rationalize<Rational>( iter->second ) ) );
        }
        ContractionCandidates candidates;
        for( auto iter = mLinearConstraints.begin(); iter != mLinearConstraints.end(); ++iter )
        {
            assert( !iter->second.empty() );
            unsigned isSatisfied = iter->first->isSatisfiedBy( mFoundSolution );
            assert( isSatisfied != 2 );
            if( isSatisfied == 0 )
            {
                candidates.insert( iter->second.begin(), iter->second.end() );
            }
        }
        for( auto candidate = mActiveNonlinearConstraints.begin(); candidate != mActiveNonlinearConstraints.end(); ++candidate )
        {
            unsigned isSatisfied = (*candidate)->constraint()->satisfiedBy( mFoundSolution );
            assert( isSatisfied != 2 );
            if( isSatisfied == 0 )
            {
                testSuccessful = false;
            }
        }
        // if a change has happened we need to restart at the latest point possible
        if( !candidates.empty() )
        {
            testSuccessful = false;
            for( auto cand : candidates )
            {
                addCandidateToRelevant( cand );
            }
            mHistoryActual->propagateStateInfeasibleConstraints();
            mHistoryActual->propagateStateInfeasibleVariables();
            setBox( mHistoryRoot );
            mHistoryActual = mHistoryActual->addRight( new icp::HistoryNode( mHistoryRoot->intervals(), 2 ) );
            mCurrentId = mHistoryActual->id();
            #ifdef ICP_MODULE_DEBUG_0
            cout << "Test point failed!" << endl;
            #endif
        }
        if( !testSuccessful )
            mFoundSolution.clear();
        // auto-activate all ICP-variables
        for( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
            (*varIt).second->autoActivate();
        return testSuccessful;
    }

//    bool ICPModule::validateSolution( bool& _newConstraintAdded )
//    {
//        vec_set_const_pFormula failedConstraints;
//        PointerSet<Formula> currentInfSet;
//        _newConstraintAdded = false;
//        #ifdef ICP_MODULE_DEBUG_0
//        cout << "Validate solution:" << endl;
//        cout << "[ICP] Call mLRAModule" << endl;
//        #endif
//        #ifdef ICP_SIMPLE_VALIDATION
//        // validate the antipoint
//        std::map<carl::Variable, double> antipoint = createModel( true );
//        EvalDoubleIntervalMap tmp;
//        for( auto iter = antipoint.begin(); iter != antipoint.end(); ++iter )
//            tmp.insert( std::make_pair( iter->first, DoubleInterval( iter->second ) ) );
//        ContractionCandidates candidates;
//        for( auto candidate = mActiveLinearConstraints.begin(); candidate != mActiveLinearConstraints.end(); ++candidate )
//        {
//            const Constraint* constraint = (*candidate)->constraint();
//            unsigned isSatisfied = constraint->consistentWith( tmp );
//            if( isSatisfied == 0 )
//            {
//                if( !(*candidate)->isActive() )
//                {
//                    candidates.insert((*candidate).first);
//                    (*candidate)->activate();
//                    _newConstraintAdded = true;
//                }
//                
//            }
//        }
//        // if a change has happened we need to restart at the latest point possible
//        if( _newConstraintAdded )
//        {
//            mHistoryActual->propagateStateInfeasibleConstraints();
//            mHistoryActual->propagateStateInfeasibleVariables();
//            icp::HistoryNode* found = tryToAddConstraint( candidates, mHistoryRoot->right() );
//            if( found == NULL )
//            {
//                setBox( mHistoryRoot );
//                mHistoryActual = mHistoryActual->addRight( new icp::HistoryNode( mHistoryRoot->intervals(), 2 ) );
//                mCurrentId = mHistoryActual->id();
//            }
//            else
//                setBox( found );
//        }
//        // autoactivate all icpVariables
//        for( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
//            (*varIt).second->autoActivate();
//        return true;
//        #else
//        // create new center constraints and add to validationFormula
//        for ( auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt)
//        {
//            if ( (*variableIt).second->checkLinear() == false )
//            {
//                carl::Variable variable = (*variableIt).second->var();
//                assert(mIntervals.find(variable) != mIntervals.end());
//                smtrat::DoubleInterval interval = mIntervals.at(variable);
//
//                smtrat::DoubleInterval center = smtrat::DoubleInterval(interval.sample());
//                Polynomial constraint = Polynomial(variable) - Polynomial(carl::rationalize<Rational>(center.sample()));
//                Formula centerTmpFormula = FormulaT( constraint, Relation::EQ );
//                mLRA.inform(centerTmpFormula->pConstraint());
//                mCenterConstraints.insert(centerTmpFormula->pConstraint());
//                mValidationFormula->push_back( centerTmpFormula );
//            }
//        }
//        
//        // assert all constraints in mValidationFormula
//        // TODO: optimize! -> should be okay to just assert centerconstraints
//        for ( auto valIt = mValidationFormula->begin(); valIt != mValidationFormula->end(); ++valIt)
//            mLRA.assertSubformula(valIt);
//
//        #ifdef ICP_MODULE_DEBUG_0
//        cout << "[mLRA] receivedFormula: " << endl;
//        cout << mLRA.rReceivedFormula().toString() << endl;
//        #endif
//        mLRA.rReceivedFormula().updateProperties();
//        Answer centerFeasible = mLRA.isConsistent();
//        mLRA.clearDeductions();
//        
//        if ( centerFeasible == True )
//        {
//            // remove centerConstaints as soon as they are not longer needed.
//            clearCenterConstraintsFromValidationFormula();
//            // strong consistency check
//            EvalRationalMap pointsolution = mLRA.getRationalModel();
//            #ifdef ICP_MODULE_DEBUG_0
//            cout << "[mLRA] Pointsolution: " << pointsolution << endl;
//            #endif
//            /*
//             * fill linear variables with pointsolution b, determine coefficients c
//             * of nonlinear variables x, take lower or upper bound correspondingly.
//             * For every active linear constraint:
//             *          check:
//             *          c*x <= e + d*b
//             * e = constant part,
//             * d = coefficient of linear variable
//             */
//
//            // For every active linear constraint:
//            for ( auto linearIt = mActiveLinearConstraints.begin(); linearIt != mActiveLinearConstraints.end(); ++linearIt)
//            {
//                Polynomial constraint = (*linearIt)->rhs();
//                Polynomial nonlinearParts;
//                Rational res = 0;
//                bool isLeftInfty = false;
//                bool isRightInfty = false;
//                bool satisfied = false;
//                
//                constraint += (*linearIt)->lhs();
//                constraint = constraint.substitute(pointsolution);
//                
//                std::map<carl::Variable, Rational> nonlinearValues;
//                
//                for( auto term = constraint.begin(); term != constraint.end(); ++term)
//                {
//                    Variables vars;
//                    if(!(*term)->monomial())
//                    {
//                        continue; // Todo: sure?
//                    }
//                    else
//                    {
//                        (*term)->monomial()->gatherVariables(vars);
//                        if( (*term)->coeff() < 0 )
//                        {
//                            for(auto varIt = vars.begin(); varIt != vars.end(); ++varIt)
//                            {
//                                if(mIntervals.at(*varIt).lowerBoundType() != BoundType::INFTY)
//                                    nonlinearValues.insert(std::make_pair(*varIt, carl::rationalize<Rational>(mIntervals.at(*varIt).lower())) );
//                                else
//                                    isLeftInfty = true;
//                            }
//                        }
//                        else
//                        {
//                            for(auto varIt = vars.begin(); varIt != vars.end(); ++varIt)
//                            {
//                                if(mIntervals.at(*varIt).upperBoundType() != BoundType::INFTY) 
//                                    nonlinearValues.insert(std::make_pair(*varIt, carl::rationalize<Rational>(mIntervals.at(*varIt).upper())) );
//                                else
//                                    isRightInfty = true;
//                            }
//                        }
//                        if( !(isLeftInfty || isRightInfty) )
//                        {  
//                            carl::Term<Rational>* tmp = (*term)->monomial()->substitute(nonlinearValues, (*term)->coeff());
//                            assert(tmp->isConstant());
//                            nonlinearParts += tmp->coeff();
//                        }
//                        nonlinearValues.clear();
//                    }
//                }
//                Rational val = 0;
//                if(constraint.isConstant())
//                {
//                    constraint += nonlinearParts;
//                    val = constraint.isZero() ? 0 : constraint.lcoeff();
//                }
//                
//                switch ((*linearIt)->constraint()->relation())
//                {
//                    case Relation::EQ: //CR_EQ = 0
//                        satisfied = (val == 0 && !isLeftInfty && !isRightInfty);
//                        break;
//                    case Relation::NEQ: //CR_NEQ = 1
//                        satisfied = (val != 0 || isLeftInfty || isRightInfty);
//                        break;
//                    case Relation::LESS: //CR_LESS = 2
//                        satisfied = (val < 0 || isLeftInfty);
//                        break;
//                    case Relation::GREATER: //CR_GREATER = 3
//                        satisfied = (val > 0 || isRightInfty);
//                        break;
//                    case Relation::LEQ: //CR_LEQ = 4
//                        satisfied = (val <= 0 || isLeftInfty);
//                        break;
//                    case Relation::GEQ: //CR_GEQ = 5
//                        satisfied = (val >= 0 || isRightInfty);
//                        break;
//                }
//                #ifdef ICP_MODULE_DEBUG_1
//                cout << "[ICP] Validate: " << *linearIt->first->constraint() << " -> " << satisfied << " (" << constraint << ") " << endl;
//                cout << "Candidate: ";
//                linearIt->first->print();
//                #endif
//                // Strong consistency check
//                if ( !satisfied )
//                {
//                    // parse mValidationFormula to get pointer to formula to generate infeasible subset
//                    for ( auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); ++formulaIt )
//                    {
//                        for( auto originIt = (*linearIt)->rOrigin().begin(); originIt != (*linearIt)->rOrigin().end(); ++originIt )
//                        {
//                            if ((*formulaIt)->pConstraint() == (*originIt)->pConstraint() )
//                            {
//                                currentInfSet.insert(*formulaIt);
//                                break;
//                            }
//                        }
//                    }
//                }
//
//            } // for every linear constraint
//            
//            if ( !currentInfSet.empty() )
//                failedConstraints.push_back(currentInfSet);
//           
//            _newConstraintAdded = updateIcpRelevantCandidates( failedConstraints );
//            return true;
//        }
//        else
//        {
//            assert( centerFeasible == False );
//            _newConstraintAdded = updateIcpRelevantCandidates( mLRA.infeasibleSubsets() );
//            clearCenterConstraintsFromValidationFormula();
//            #ifdef ICP_MODULE_DEBUG_0
//            if( _newConstraintAdded )
//                cout << "New ICP-relevant contraction candidates added!" << endl; 
//            cout << "Validation failed!" << endl;
//            #endif
//            return false;
//        }
//        #endif
//    }
//    
//    bool ICPModule::updateIcpRelevantCandidates( const vec_set_const_pFormula& _infSubsetsInLinearization )
//    {
//        bool newConstraintAdded = false;
//        ContractionCandidates candidates;
//        // TODO: Das muss effizienter gehen! CORRECT?
//        for ( auto vecIt = _infSubsetsInLinearization.begin(); vecIt != _infSubsetsInLinearization.end(); ++vecIt )
//        {
//            for ( auto infSetIt = (*vecIt).begin(); infSetIt != (*vecIt).end(); ++infSetIt )
//            {
//                // if the failed constraint is not a centerConstraint - Ignore centerConstraints
//                if ( mCenterConstraints.find((*infSetIt)->pConstraint()) == mCenterConstraints.end() )
//                {
//                    // add candidates for all variables to icpRelevantConstraints  
//                    auto iterB = mDeLinearizations.find( *infSetIt );
//                    if ( iterB != mDeLinearizations.end() )
//                    {
//                        // search for the candidates and add them as icpRelevant
//                        for ( icp::ContractionCandidate* actCandidateIt : mActiveLinearConstraints )
//                        {
//                            if ( actCandidateIt->hasOrigin( iterB->second ) )
//                            {
//                                #ifdef ICP_MODULE_DEBUG_1                               
//                                cout << "isActive ";
//                                actCandidateIt->print();
//                                cout <<  " : " << actCandidateIt->isActive() << endl;
//                                #endif
//
//                                // if the candidate is not active we really added a constraint -> indicate the change
//                                if ( !actCandidateIt->isActive() )
//                                {
//                                    actCandidateIt->activate();
//                                    candidates.insert( actCandidateIt );
//                                    newConstraintAdded = true;
//                                }
//
//                                // activate all icpVariables for that candidate
//                                for ( auto variableIt = actCandidateIt->constraint()->variables().begin(); variableIt != actCandidateIt->constraint()->variables().end(); ++variableIt )
//                                {
//                                    std::map<carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
//                                    assert(icpVar != mVariables.end());
//                                    (*icpVar).second->activate();
//                                }
//                            } // found correct linear replacement
//                        } // iterate over active linear constraints
//                    } // is a linearization replacement
//                    else
//                    {
//                        // this should not happen
//                        assert(false);
//                    }
//                } // is no center constraint
//            }
//        }
//            
//        if(newConstraintAdded)
//        {
//            mHistoryActual->propagateStateInfeasibleConstraints();
//            mHistoryActual->propagateStateInfeasibleVariables();
//            icp::HistoryNode* found = tryToAddConstraint(candidates, mHistoryRoot->right());
//            if(found == NULL)
//            {
//                setBox(mHistoryRoot);
//                mHistoryActual = mHistoryActual->addRight(new icp::HistoryNode(mHistoryRoot->intervals(),2));
//                mCurrentId = mHistoryActual->id();
//                assert( mCurrentId == 2);
//            }
//            else
//                setBox(found);
//        }
//        return newConstraintAdded;
//    }
    
    void ICPModule::clearCenterConstraintsFromValidationFormula()
    {
        for( auto centerIt = mValidationFormula->begin(); centerIt != mValidationFormula->end(); )
        {
            if( mCenterConstraints.find( centerIt->formula().pConstraint()) != mCenterConstraints.end() )
            {
                mLRA.removeSubformula( centerIt );
                centerIt = mValidationFormula->erase( centerIt );
            }
            else
                ++centerIt;
        }
        mCenterConstraints.clear();
    }
    
    bool ICPModule::checkBoxAgainstLinearFeasibleRegion()
    {
        std::set<FormulaT> addedBoundaries = createConstraintsFromBounds(mIntervals);
        for( auto formulaIt = addedBoundaries.begin(); formulaIt != addedBoundaries.end();  )
        {
            auto res = mValidationFormula->add( *formulaIt );
            if( res.second )
            {
                assert( res.first == mValidationFormula->end() );
                mLRA.inform( *formulaIt );
                mLRA.assertSubformula( res.first );
				++formulaIt;
            }
			else
			{
				formulaIt = addedBoundaries.erase(formulaIt);
			}
        }
        mValidationFormula->updateProperties();
        Answer boxCheck = mLRA.isConsistent();
        #ifdef ICP_MODULE_DEBUG_0
        cout << "Boxcheck: " << ANSWER_TO_STRING(boxCheck) << endl;
        #endif
        #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
        if ( boxCheck == False )
        {
            FormulaT* actualAssumptions = new FormulaT(*mValidationFormula);
            Module::addAssumptionToCheck(*actualAssumptions,false,"ICP_BoxValidation");
        }
        #endif
        assert( boxCheck != Unknown );
        if( boxCheck != True )
        {
            vec_set_const_pFormula tmpSet = mLRA.infeasibleSubsets();
            for ( auto infSetIt = tmpSet.begin(); infSetIt != tmpSet.end(); ++infSetIt )
            {
                for ( auto formulaIt = (*infSetIt).begin(); formulaIt != (*infSetIt).end(); ++formulaIt )
                {
                    if( !formulaIt->pConstraint()->isBound() )
                    {
                        mHistoryActual->addInfeasibleConstraint(formulaIt->pConstraint());
                        for( auto variableIt = formulaIt->constraint().variables().begin(); variableIt != formulaIt->constraint().variables().end(); ++variableIt )
                        {
                            assert( mVariables.find(*variableIt) != mVariables.end() );
                            mHistoryActual->addInfeasibleVariable(mVariables.at(*variableIt));
                        }
                    }
                    else
                    {
                        assert( mVariables.find( *formulaIt->pConstraint()->variables().begin() ) != mVariables.end() );
                        mHistoryActual->addInfeasibleVariable( mVariables.at( *formulaIt->pConstraint()->variables().begin()) );
                    }
                }
            }
        }
        #ifdef ICP_PROLONG_CONTRACTION
        else
        {
            EvalRationalIntervalMap bounds = mLRA.getVariableBounds();
            #ifdef ICP_MODULE_DEBUG_0
            cout << "Newly obtained Intervals: " << endl;
            #endif
            for ( auto boundIt = bounds.begin(); boundIt != bounds.end(); ++boundIt )
            {
                assert( mVariables.find((*boundIt).first) != mVariables.end() );
                icp::IcpVariable& icpVar = *mVariables.find((*boundIt).first)->second;
                RationalInterval tmp = (*boundIt).second;
                const DoubleInterval& icpVarInterval = icpVar.interval();
                // mHistoryRoot->addInterval((*boundIt).first, smtrat::DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType()) );
                DoubleInterval newInterval = DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType() );
                if( !(icpVarInterval == newInterval) && icpVarInterval.contains(newInterval) )
                {
                    #ifdef ICP_MODULE_DEBUG_0
                    cout << (*boundIt).first << ": " << (*boundIt).second << endl;
                    #endif
                    double relativeContraction = (icpVarInterval.diameter() - newInterval.diameter()) / icpVarInterval.diameter();
                    icpVar.setInterval( newInterval );
                    updateRelevantCandidates((*boundIt).first, relativeContraction);
                }
            }
            
            // get intervals for slackvariables
            const LRAModule<LRASettings1>::ExVariableMap slackVariables = mLRA.slackVariables();
            for ( auto slackIt = slackVariables.begin(); slackIt != slackVariables.end(); ++slackIt )
            {
                std::map<const LRAVariable*, ContractionCandidates>::iterator linIt = mLinearConstraints.find((*slackIt).second);
                if ( linIt != mLinearConstraints.end() )
                {
                    // dirty hack: expect lhs to be set and take first item of set of CCs --> Todo: Check if it is really set in the constructors of the CCs during inform and assert
                    RationalInterval tmp = (*slackIt).second->getVariableBounds();
                    // keep root updated about the initial box.
                    // mHistoryRoot->rIntervals()[(*(*linIt).second.begin())->lhs()] = smtrat::DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType());
                    DoubleInterval newInterval = DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType() );
                    carl::Variable var = (*(*linIt).second.begin())->lhs();
                    icp::IcpVariable& icpVar = *mVariables.at(var);
                    const DoubleInterval& icpVarInterval = icpVar.interval();
                    if( !(icpVarInterval == newInterval) && icpVarInterval.contains(newInterval) )
                    {
                        double relativeContraction = (icpVarInterval.diameter() - newInterval.diameter()) / icpVarInterval.diameter();
                        icpVar.setInterval( newInterval );
                        updateRelevantCandidates(var, relativeContraction);
                        #ifdef ICP_MODULE_DEBUG_1
                        cout << "Added interval (slackvariables): " << var << " " << tmp << endl;
                        #endif
                    }
                }
            }
        }
        #endif
        
        // remove boundaries from mLRA module after boxChecking.
        for( auto boundIt = addedBoundaries.begin(); boundIt != addedBoundaries.end(); )
        {
            auto pos = mValidationFormula->find( *boundIt );
            if( pos != mValidationFormula->end() )
            {
                mLRA.removeSubformula( pos );
                mValidationFormula->erase( pos );
            }
            boundIt = addedBoundaries.erase(boundIt);
        }
        
        mLRA.clearDeductions();
        assert(addedBoundaries.empty());
        
        if ( boxCheck == True )
            return true;
        return false;
    }
    
    bool ICPModule::chooseBox()
    {
        mLastCandidate = NULL;
        icp::HistoryNode* newBox = chooseBox( mHistoryActual );
        if ( newBox != NULL )
        {
            setBox(newBox);
            return true;
        }
        else
        {
            // no new Box to select -> finished
            // TODO: If chooseBox worked properly, this wouldn't be necessary.
            mHistoryActual->propagateStateInfeasibleConstraints();
            mHistoryActual->propagateStateInfeasibleVariables();

            mInfeasibleSubsets.clear();
            mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
            // printInfeasibleSubsets();
            return false;
        }
    }
    
    icp::HistoryNode* ICPModule::chooseBox( icp::HistoryNode* _basis )
    {
        if ( _basis->isLeft() )
        {
            // if spliting constraint or the constraint resulting from a contraction
            // of the splitting constraint is included in the infeasible subset
            // skip the right box and continue.
            carl::Variable variable = _basis->variable();
            assert( mIntervals.find(variable) != mIntervals.end() );
            if ( _basis->stateInfeasibleConstraintsContainSplit() )
            {
                // set infeasible subset
                for( auto constraintIt = _basis->rStateInfeasibleConstraints().begin(); constraintIt != _basis->rStateInfeasibleConstraints().end(); ++constraintIt )
                    _basis->parent()->addInfeasibleConstraint(*constraintIt);
                
                for( auto variableIt = _basis->rStateInfeasibleVariables().begin(); variableIt != _basis->rStateInfeasibleVariables().end(); ++variableIt )
                    _basis->parent()->addInfeasibleVariable(*variableIt,true);
            }
            else
            {
                if ( _basis->parent() == NULL )
                {
                    // should not happen: Root is defined to be a right-child
                    assert(false);
                    return NULL;
                }
                else
                {
                    // skip the right box
                    // set infeasible subset
                    for( auto constraintIt = _basis->rStateInfeasibleConstraints().begin(); constraintIt != _basis->rStateInfeasibleConstraints().end(); ++constraintIt )
                        _basis->parent()->addInfeasibleConstraint(*constraintIt);
                    
                    for( auto variableIt = _basis->rStateInfeasibleVariables().begin(); variableIt != _basis->rStateInfeasibleVariables().end(); ++variableIt )
                        _basis->parent()->addInfeasibleVariable(*variableIt,true);
                    
                    chooseBox(_basis->parent());
                }
            }
            return _basis->parent()->right();
        }
        else // isRight
        {
            if ( _basis->parent() == mHistoryRoot )
            {
                // set infeasible subset
                for( auto constraintIt = _basis->rStateInfeasibleConstraints().begin(); constraintIt != _basis->rStateInfeasibleConstraints().end(); ++constraintIt )
                    _basis->parent()->addInfeasibleConstraint(*constraintIt);
                
                for( auto variableIt = _basis->rStateInfeasibleVariables().begin(); variableIt != _basis->rStateInfeasibleVariables().end(); ++variableIt )
                    _basis->parent()->addInfeasibleVariable(*variableIt,true);
                
                return NULL;
            }
            else // select next starting from parent
            {
                // set infeasible subset
                for( auto constraintIt = _basis->rStateInfeasibleConstraints().begin(); constraintIt != _basis->rStateInfeasibleConstraints().end(); ++constraintIt )
                    _basis->parent()->addInfeasibleConstraint(*constraintIt);
                
                for( auto variableIt = _basis->rStateInfeasibleVariables().begin(); variableIt != _basis->rStateInfeasibleVariables().end(); ++variableIt )
                    _basis->parent()->addInfeasibleVariable(*variableIt,true);
                
                return chooseBox( _basis->parent() );
            }
        }
    }

    void ICPModule::pushBoundsToPassedFormula()
    {
        Variables originalRealVariables;
        rReceivedFormula().realValuedVars( originalRealVariables );
        for( std::map<carl::Variable, icp::IcpVariable*>::iterator iter = mVariables.begin(); iter != mVariables.end(); ++iter )
        {
            carl::Variable::Arg tmpSymbol = iter->first;
            icp::IcpVariable& icpVar = *iter->second;
            if( icpVar.isOriginal() && originalRealVariables.find( tmpSymbol ) != originalRealVariables.end() )
            {
                if( icpVar.isExternalUpdated() != icp::Updated::NONE )
                {
                    auto varIntervalPair = mIntervals.find( tmpSymbol );
                    assert( varIntervalPair != mIntervals.end() );
                    DoubleInterval& interval = varIntervalPair->second;
                    icp::Updated icpVarExUpdated = icpVar.isExternalUpdated();
                    // generate both bounds, left first
                    if( icpVarExUpdated == icp::Updated::BOTH || icpVarExUpdated == icp::Updated::LEFT )
                    {
                        Rational bound = carl::rationalize<Rational>( interval.lower() );
                        Poly leftEx = Poly( tmpSymbol ) - Poly(bound);

                        FormulaT leftTmp;
                        switch( interval.lowerBoundType() )
                        {
                            case carl::BoundType::STRICT:
                                leftTmp = FormulaT( leftEx, Relation::GREATER );
                                break;
                            case carl::BoundType::WEAK:
                                leftTmp = FormulaT( leftEx, Relation::GEQ );
                                break;
                            default:
                                break;
                        }
                        if( icpVar.externalLeftBound() != passedFormulaEnd() )
                            Module::eraseSubformulaFromPassedFormula( icpVar.externalLeftBound(), true );
                        if ( leftTmp.isTrue() )
                        {
                            icpVar.setExternalLeftBound( passedFormulaEnd() );
                        }
                        else
                        {
                            addConstraintToInform( leftTmp );
                            vec_set_const_pFormula origins;
                            origins.push_back( std::set<FormulaT>() );
                            auto res = addSubformulaToPassedFormula( leftTmp, std::move( origins ) );
                            if( res.second )
                            {
                                icpVar.setExternalLeftBound( res.first );
                            }
                        }
                    }
                    
                    if( icpVarExUpdated == icp::Updated::BOTH || icpVarExUpdated == icp::Updated::RIGHT )
                    {
                        // right:
                        Rational bound = carl::rationalize<Rational>( interval.upper() );
                        Poly rightEx = Poly( tmpSymbol ) - Poly( bound );
                        FormulaT rightTmp;
                        switch( interval.upperBoundType() )
                        {
                            case carl::BoundType::STRICT:
                                rightTmp = FormulaT( rightEx, Relation::LESS );
                                break;
                            case carl::BoundType::WEAK:
                                rightTmp = FormulaT( rightEx, Relation::LEQ );
                                break;
                            default:
                                break;
                        }
                        if( icpVar.externalRightBound() != passedFormulaEnd() )
                            Module::eraseSubformulaFromPassedFormula( icpVar.externalRightBound(), true );
                        if( rightTmp.isTrue() )
                        {
                            icpVar.setExternalRightBound( passedFormulaEnd() );
                        }
                        else
                        {
                            addConstraintToInform( rightTmp );
                            vec_set_const_pFormula origins;
                            origins.push_back( std::set<FormulaT>() );
                            auto res = addSubformulaToPassedFormula( rightTmp, origins );
                            if( res.second )
                            {
                                icpVar.setExternalRightBound( res.first );
                            }
                        }
                    }
                    icpVar.setExternalUnmodified();
                }
            }
        }
    }
    
    std::set<FormulaT> ICPModule::variableReasonHull( icp::set_icpVariable& _reasons )
    {
        std::set<FormulaT> reasons;
        for( auto variableIt = _reasons.begin(); variableIt != _reasons.end(); ++variableIt )
        {
            if ((*variableIt)->lraVar() != NULL)
            {
                std::set<FormulaT> definingOrigins = (*variableIt)->lraVar()->getDefiningOrigins();
                for( auto formulaIt = definingOrigins.begin(); formulaIt != definingOrigins.end(); ++formulaIt )
                {
                    // cout << "Defining origin: " << **formulaIt << " FOR " << *(*variableIt) << endl;
                    bool hasAdditionalVariables = false;
                    Variables realValuedVars;
                    rReceivedFormula().realValuedVars(realValuedVars);
                    for( auto varIt = realValuedVars.begin(); varIt != realValuedVars.end(); ++varIt )
                    {
                        if(*varIt != (*variableIt)->var() && formulaIt->constraint().hasVariable(*varIt))
                        {
                            hasAdditionalVariables = true;
                            break;
                        }
                    }
                    if( hasAdditionalVariables)
                    {
                        // cout << "Addidional variables." << endl;
                        for( auto receivedFormulaIt = rReceivedFormula().begin(); receivedFormulaIt != rReceivedFormula().end(); ++receivedFormulaIt )
                        {
                            if( receivedFormulaIt->formula().constraint().hasVariable((*variableIt)->var()) && receivedFormulaIt->formula().constraint().isBound() )
                            {
                                reasons.insert( receivedFormulaIt->formula() );
                                // cout << "Also add: " << **receivedFormulaIt << endl;
                            }
                        }
                    }
                    else
                    {
                        // cout << "No additional variables." << endl;
                        auto replacementIt = mDeLinearizations.find( *formulaIt );
                        assert( replacementIt != mDeLinearizations.end() ); // TODO (from Florian): Do we need this?
                        reasons.insert((*replacementIt).second);
                    } // has no additional variables
                } // for all definingOrigins
            }
        }
        return reasons;
    }
    
    std::set<FormulaT> ICPModule::constraintReasonHull( const std::set<const ConstraintT*>& _reasons )
    {
        std::set<FormulaT> reasons;
        for ( auto constraintIt = _reasons.begin(); constraintIt != _reasons.end(); ++constraintIt )
        {
            for ( auto formulaIt = rReceivedFormula().begin(); formulaIt != rReceivedFormula().end(); ++formulaIt )
            {
                if ( *constraintIt == formulaIt->formula().pConstraint() )
                {
                    reasons.insert( formulaIt->formula() );
                    break;
                }
            }
        }
        return reasons;
    }
    
    std::set<FormulaT> ICPModule::createConstraintsFromBounds( const EvalDoubleIntervalMap& _map )
    {
        std::set<FormulaT> addedBoundaries;
        Variables originalRealVariables;
        rReceivedFormula().realValuedVars(originalRealVariables);
        for ( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
        {
            carl::Variable tmpSymbol = *variablesIt;
            if ( _map.find(tmpSymbol) != _map.end() )
            {
                std::map<carl::Variable, icp::IcpVariable*>::iterator pos = mVariables.find(tmpSymbol);
                if ( pos != mVariables.end() )
                {
                    if( (*pos).second->isInternalBoundsSet() == icp::Updated::BOTH && (*pos).second->isInternalUpdated() == icp::Updated::NONE )
                    {
                        addedBoundaries.insert((*pos).second->internalLeftBound());
                        addedBoundaries.insert((*pos).second->internalRightBound());
                    }
                    else
                    {
                        std::pair<const ConstraintT*, const ConstraintT*> boundaries = icp::intervalToConstraint(tmpSymbol, _map.at(tmpSymbol));
                        icp::Updated inBoundsSet = (*pos).second->isInternalBoundsSet();
                        icp::Updated inBoundsUpdated = (*pos).second->isInternalUpdated();
                        if( boundaries.second != NULL && 
                            (inBoundsUpdated == icp::Updated::BOTH || inBoundsUpdated == icp::Updated::RIGHT || inBoundsSet == icp::Updated::NONE || inBoundsSet == icp::Updated::LEFT) )
                        {
                            assert( boundaries.second->isConsistent() == 2 );
                            FormulaT rightBound = FormulaT(boundaries.second);
                            (*pos).second->setInternalRightBound(rightBound);
                            addedBoundaries.insert(rightBound);
                            #ifdef ICP_MODULE_DEBUG_1
                            cout << "Created upper boundary constraint: " << *rightBound << endl;
                            #endif
                        }
                        if( boundaries.first != NULL && 
                            (inBoundsUpdated == icp::Updated::BOTH || inBoundsUpdated == icp::Updated::LEFT || inBoundsSet == icp::Updated::NONE || inBoundsSet == icp::Updated::RIGHT) )
                        {
                            assert( boundaries.first->isConsistent() == 2 );
                            FormulaT leftBound = FormulaT(boundaries.first);
                            (*pos).second->setInternalLeftBound(leftBound);
                            addedBoundaries.insert(leftBound);
                            #ifdef ICP_MODULE_DEBUG_1
                            cout << "Created lower boundary constraint: " << *leftBound << endl;
                            #endif
                        }
                    }
                }
            }
        }
        return addedBoundaries;
    }
    
    FormulaT ICPModule::transformDeductions( const FormulaT& _deduction )
    {
        if( _deduction.getType() == FormulaType::CONSTRAINT )
        {
            auto iter = mDeLinearizations.find( _deduction );
            if( iter == mDeLinearizations.end() )
            {
                const ConstraintT& c = _deduction.constraint();
                return *mCreatedDeductions.insert( FormulaT( c.lhs().substitute(mSubstitutions), c.relation() ) ).first;
            } 
            else
            {
                return iter->second;
            }
        }
        else if( _deduction.getType() == NOT )
        {
            return FormulaT( FormulaType::NOT, transformDeductions( _deduction.subformula() ) );
        }
        else if( _deduction.isBooleanCombination() )
        {
            std::set<FormulaT> subformulas;
            for( const FormulaT& subformula : _deduction.subformulas() )
            {
                subformulas.insert( transformDeductions( subformula ) );
            }
            FormulaT deduction = FormulaT( _deduction.getType(), subformulas );
            mCreatedDeductions.insert( deduction );
            return deduction;
        }
        else
        {
            //should not happen
            assert(false);
            return FormulaT( carl::FormulaType::TRUE );
        }
    }
    
    void ICPModule::remapAndSetLraInfeasibleSubsets()
    {
        vec_set_const_pFormula tmpSet = mLRA.infeasibleSubsets();
        for ( auto infSetIt = tmpSet.begin(); infSetIt != tmpSet.end(); ++infSetIt )
        {
            std::set<FormulaT> newSet;
            for ( auto formulaIt = (*infSetIt).begin(); formulaIt != (*infSetIt).end(); ++formulaIt )
            {
                auto delinIt = mDeLinearizations.find(*formulaIt);
                assert( delinIt != mDeLinearizations.end() ); 
                assert( std::find( rReceivedFormula().begin(), rReceivedFormula().end(), delinIt->second ) != rReceivedFormula().end());
                newSet.insert( delinIt->second );
            }
            assert(newSet.size() == (*infSetIt).size());
            mInfeasibleSubsets.push_back(newSet);
        }
    }

    //#ifdef BOXMANAGEMENT
    void ICPModule::setBox( icp::HistoryNode* _selection )
    {
        assert(_selection != NULL);
        #ifdef ICP_MODULE_DEBUG_0
        cout << "Set box -> " << _selection->id() << ", #intervals: " << mIntervals.size() << " -> " << _selection->intervals().size() << endl;
        #endif
        // set intervals - currently we don't change not contained intervals.
        for ( auto constraintIt = _selection->rIntervals().begin(); constraintIt != _selection->rIntervals().end(); ++constraintIt )
        {
            assert(mIntervals.find((*constraintIt).first) != mIntervals.end());
            // only update intervals which changed
            if ( !(mIntervals.at((*constraintIt).first)==(*constraintIt).second) )
            {
                std::map<carl::Variable, icp::IcpVariable*>::const_iterator icpVar = mVariables.find((*constraintIt).first);
                // cout << "Searching for " << (*intervalIt).first.get_name() << endl;
                assert(icpVar != mVariables.end());
                (*icpVar).second->setInterval( (*constraintIt).second );
            }
        }
        // set actual node as selection
        mHistoryActual = _selection;
        mHistoryActual->removeLeftChild();
        mHistoryActual->removeRightChild();
        
        if(mHistoryActual->isLeft())
            mCurrentId = mHistoryActual->id()+1;
        else
            mCurrentId = mHistoryActual->id();
        
        assert(mHistoryActual->isRight() && !mHistoryActual->isLeft());
        if (mHistoryActual->parent() != NULL && mHistoryActual->isRight() )
            mHistoryActual->parent()->removeLeftChild();
    }
    
    icp::HistoryNode* ICPModule::tryToAddConstraint( const ContractionCandidates& _candidates, icp::HistoryNode* _node )
    {
        if(_node != NULL)
        {
            bool contracted = false;
            double relativeContraction;
            EvalDoubleIntervalMap intervals;
            intervals.insert(_node->intervals().begin(), _node->intervals().end());
            assert(intervals.size() != 0);
            for( auto candidateIt = _candidates.begin(); candidateIt !=  _candidates.end(); ++candidateIt )
            {
                relativeContraction = 0;
                tryContraction(*candidateIt, relativeContraction, intervals);
                contracted = relativeContraction > 0;
                if(contracted)
                    break;
            }
            if (contracted)
                return _node;
            else
            {
                // left-most outer-most
                icp::HistoryNode* success = tryToAddConstraint(_candidates, _node->left());
                if (success == NULL)
                    success = tryToAddConstraint(_candidates, _node->right());
                return success;
            }
        }
        return NULL;
    }
    
    std::set<FormulaT> ICPModule::collectReasons( icp::HistoryNode* _node )
    {
        icp::set_icpVariable variables = _node->rStateInfeasibleVariables();
        for( auto varIt = variables.begin(); varIt != variables.end(); ++varIt )
        {
            // cout << "Collect Hull for " << (*varIt)->var().get_name() << endl;
            _node->variableHull((*varIt)->var(), variables);
        }
        std::set<FormulaT> reasons = variableReasonHull(variables);
        std::set<FormulaT> constraintReasons = constraintReasonHull(_node->rStateInfeasibleConstraints());
        reasons.insert(constraintReasons.begin(), constraintReasons.end());
        return reasons;
    }
    //#endif
    
    bool ICPModule::intervalsEmpty( bool _original ) const
    {
        for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
        {
            auto varIt = mVariables.find((*constraintIt).first);
            //assert( varIt != mVariables.end() );//TODO (from FLorian): can we assume this?
            if( !_original || (varIt != mVariables.end() && varIt->second->isOriginal()))
            {
                if( (*constraintIt).second.isEmpty() ) return true;
            }
        }
        return false;
    }
    
    #ifdef ICP_BOXLOG
    void ICPModule::writeBox()
    {
        GiNaC::symtab originalRealVariables = rReceivedFormula().realValuedVars();
        
        for ( auto varIt = originalRealVariables.begin(); varIt != originalRealVariables.end(); ++varIt )
        {
            icpLog << "; " << (*varIt).first;
            if ( mIntervals.find(ex_to<symbol>((*varIt).second)) != mIntervals.end() )
            {
                icpLog << "[";
                if ( mIntervals[ex_to<symbol>((*varIt).second)].lowerBoundType() == carl::BoundType::INFTY )
                {
                    icpLog << "INF";
                }
                else
                {
                    icpLog << mIntervals[ex_to<symbol>((*varIt).second)].lower();
                }
                icpLog << ",";
                if ( mIntervals[ex_to<symbol>((*varIt).second)].upperBoundType() == carl::BoundType::INFTY )
                {
                    icpLog << "INF";
                }
                else
                {
                    icpLog << mIntervals[ex_to<symbol>((*varIt).second)].upper();
                }
                icpLog << "]";
            }
        }
        icpLog << "\n";
    }
    #endif
    
    void ICPModule::debugPrint()
    {
        cout << "********************* linear Constraints **********************" << endl;
        for( auto linearIt = mLinearConstraints.begin(); linearIt != mLinearConstraints.end(); ++linearIt){
            for ( auto candidateIt = (*linearIt).second.begin(); candidateIt != (*linearIt).second.end(); ++candidateIt )
            {
                const ConstraintT* constraint = (*candidateIt)->constraint();
                cout << (*candidateIt)->id() << ": " << *constraint << endl;
            }
        }
        cout << "****************** active linear constraints ******************" << endl;
        for(auto activeLinearIt = mActiveLinearConstraints.begin(); activeLinearIt != mActiveLinearConstraints.end(); ++activeLinearIt){
            cout << "Count: " << (*activeLinearIt)->activity() << " , ";
            (*activeLinearIt)->print();
        }
        cout << "******************* active linear variables *******************" << endl;
        for (auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt )
        {
            if ( (*variableIt).second->checkLinear() )
                cout << (*variableIt).first << ", ";
        }
        cout << endl;
        cout << "******************** nonlinear constraints ********************" << endl;
        std::map<const ConstraintT*, ContractionCandidates>::iterator nonlinearIt;
        ContractionCandidates::iterator replacementsIt;

        for(nonlinearIt = mNonlinearConstraints.begin(); nonlinearIt != mNonlinearConstraints.end(); ++nonlinearIt){
            cout << *(*nonlinearIt).first << endl;
            cout << "\t replacements: " << endl;
            for(replacementsIt = nonlinearIt->second.begin(); replacementsIt != nonlinearIt->second.end(); ++replacementsIt)
            {
                cout << "   ";
                (*replacementsIt)->print();
            }
        }
        cout << "**************** active nonlinear constraints *****************" << endl;
        for( auto activeNonlinearIt = mActiveNonlinearConstraints.begin(); activeNonlinearIt != mActiveNonlinearConstraints.end(); ++activeNonlinearIt )
        {
            cout << "Count: " << (*activeNonlinearIt)->activity() << " , ";
            (*activeNonlinearIt)->print();
        }
        cout << "***************** active nonlinear variables ******************" << endl;
        for (auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt )
        {
            if ( (*variableIt).second->checkLinear() == false )
                cout << (*variableIt).first << ", ";
        }
        cout << endl;
        cout << "************************** Intervals **************************" << endl;
        for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
        {
            cout << (*constraintIt).first << "  \t -> \t" << (*constraintIt).second << endl;
        }
        cout << endl;
        cout << "************************* Linearizations ************************" << endl;
        for ( auto replacementIt = mLinearizations.begin(); replacementIt != mLinearizations.end(); ++replacementIt )
        {
            cout << (*replacementIt).first << "  \t -> \t" << (*replacementIt).second << endl;
        }
        cout <<endl;
        cout << "************************* Delinearizations ************************" << endl;
        for ( auto replacementIt = mDeLinearizations.begin(); replacementIt != mDeLinearizations.end(); ++replacementIt )
        {
            cout << (*replacementIt).first << "  \t -> \t" << (*replacementIt).second << endl;
        }
        cout <<endl;
        cout << "************************* ICP Variables ***********************" << endl;
        for ( auto variablesIt = mVariables.begin(); variablesIt != mVariables.end(); ++variablesIt )
            (*variablesIt).second->print();
        
        cout << endl;
        cout << "*********************** ValidationFormula *********************" << endl;
        cout << mValidationFormula->toString() << endl;
        cout << "***************************************************************" << endl;
        
        cout << "************************* Substitution ************************" << endl;
        for( auto subsIt = mSubstitutions.begin(); subsIt != mSubstitutions.end(); ++subsIt )
            cout << (*subsIt).first << " -> " << (*subsIt).second << endl;
        
        cout << "***************************************************************" << endl;
    }
    
    void ICPModule::printAffectedCandidates()
    {
        for ( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
        {
            for ( auto candidateIt = (*varIt).second->candidates().begin(); candidateIt != (*varIt).second->candidates().end(); ++candidateIt)
            {
                cout << (*varIt).first << "\t -> ";
                (*candidateIt)->print();
            }
        }
    }

    void ICPModule::printIcpVariables()
    {
        for ( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
            (*varIt).second->print();
    }

    void ICPModule::printIcpRelevantCandidates()
    {
        cout << "Size icpRelevantCandidates: " << mIcpRelevantCandidates.size() << endl;
        for ( auto candidateIt = mIcpRelevantCandidates.begin(); candidateIt != mIcpRelevantCandidates.end(); ++candidateIt )
        {
            cout << (*candidateIt).first << " \t " << (*candidateIt).second <<"\t Candidate: ";
            icp::ContractionCandidate* cc = mCandidateManager->getInstance()->getCandidate((*candidateIt).second);
            assert( cc != NULL );
            cc->print();
        }
    }

    void ICPModule::printIntervals( bool _original )
    {
        for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
        {
            auto varIt = mVariables.find((*constraintIt).first);
            //assert( varIt != mVariables.end() );//TODO (from FLorian): can we assume this?
            if( !_original || (varIt != mVariables.end() && varIt->second->isOriginal()))
            {
                cout << (*constraintIt).first << " \t -> " << (*constraintIt).second << endl;
            }
        }
    }
} // namespace smtrat
