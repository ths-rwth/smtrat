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

#include "ICPModule.h"
#include "assert.h"

using namespace std;
using namespace carl;

//#define ICPMODULE_DEBUG
//#define ICPMODULE_REDUCED_DEBUG
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
        mReplacements(),
        mLinearizations(),
        mSubstitutions(),
        mHistoryRoot(new icp::HistoryNode(mIntervals,1)),
        mHistoryActual(NULL),
        mValidationFormula(new ModuleInput()),
//        mReceivedFormulaMapping(),
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
        mTargetDiameter(0.01),
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
        delete mHistoryRoot;
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

    bool ICPModule::inform( const Constraint* const _constraint )
    {
        #ifdef ICPMODULE_DEBUG
        cout << "[ICP] inform: " << (*_constraint) << " (id: " << _constraint->id() << ")" << endl;
        #endif  
        // do not inform about boundary constraints - this leads to confusion
        if ( !_constraint->isBound() )
            Module::inform(_constraint);

        if( _constraint->variables().size() > 0 )
        {
            const Polynomial constr = _constraint->lhs();
            bool linear = false;
            // add original variables to substitution mapping
            for( auto variablesIt = _constraint->variables().begin(); variablesIt != _constraint->variables().end(); ++variablesIt )
            {
                if( mSubstitutions.find(*variablesIt) == mSubstitutions.end() )
                {
                    mSubstitutions.insert(std::make_pair(*variablesIt, Polynomial(*variablesIt)));
                }
            }

            // actual preprocessing
            FastMap<Polynomial, const Constraint*> temporaryMonomes;
            linear = icp::isLinear( _constraint, constr, temporaryMonomes );
            const Formula* linearFormula;
            bool informLRA = true;
            
            if ( linear )
                linearFormula = newFormula( _constraint );
            else
            {
                Polynomial lhs;
                if(!temporaryMonomes.empty())
                    lhs = createContractionCandidates(temporaryMonomes);
                else
                {
                    for( auto replacementsIt = mReplacements.begin(); replacementsIt != mReplacements.end(); ++replacementsIt )
                    {
                        if ( (*replacementsIt).second->pConstraint() == _constraint )
                        {
                            lhs = (*replacementsIt).first->constraint().lhs();
                            break;
                        }
                    }
                    informLRA = false;
                    assert(!lhs.isZero());
                }
                
                assert(temporaryMonomes.empty());
                
                if( informLRA )
                {
                    linearFormula = newFormula( newConstraint( lhs, _constraint->relation() ) );
                }
            }
            if( informLRA )
            {
                // store replacement for later comparison when asserting
                mReplacements[linearFormula] = newFormula( _constraint );
                // inform internal LRAmodule of the linearized constraint
                mLRA.inform(linearFormula->pConstraint());
                #ifdef ICPMODULE_DEBUG
                cout << "[mLRA] inform: " << linearFormula->constraint() << endl;
                #endif
                assert( linearFormula->constraint().lhs().isLinear() );
            }
        }
        return (_constraint->isConsistent() != 0);
    }


    bool ICPModule::assertSubformula( ModuleInput::const_iterator _formula )
    {
        const Constraint* constr = (*_formula)->pConstraint();

        // create and initialize slackvariables
        mLRA.init();
        if( !mIsIcpInitialized)
        {
            // catch deductions
            mLRA.init();
            mLRA.updateDeductions();
            while( !mLRA.deductions().empty() )
            {
                #ifdef ICPMODULE_DEBUG
                #ifndef ICPMODULE_REDUCED_DEBUG
                cout << "Create deduction for: " << mLRA.deductions().back()->toString(false,0,"",true,true,true ) << endl;
                #endif
                #endif
                const Formula* deduction = transformDeductions( mLRA.deductions().back() );
                mCreatedDeductions.insert(deduction);
                mLRA.rDeductions().pop_back();
                addDeduction(deduction);
                #ifdef ICPMODULE_DEBUG
                #ifndef ICPMODULE_REDUCED_DEBUG
                cout << "Passed deduction: " << deduction->toString(false,0,"",true,true,true ) << endl;
                #endif
                #endif
            }
            mIsIcpInitialized = true;
        }
        #ifdef ICPMODULE_DEBUG
        cout << "[ICP] Assertion: " << *constr << endl;
        #endif
        assert( (*_formula)->getType() == CONSTRAINT );
        //if ( (*_formula)->constraint().variables().size() > 1 || (mNonlinearConstraints.find((*_formula)->pConstraint()) != mNonlinearConstraints.end()) )
        if( !(*_formula)->constraint().isBound() )
        {
            addSubformulaToPassedFormula( *_formula, *_formula );
            Module::assertSubformula( _formula );
        }
        
        /**
         * activate associated nonlinear contraction candidates.
         */
        if (mNonlinearConstraints.find(constr) != mNonlinearConstraints.end())
        {
            #ifdef ICPMODULE_DEBUG
            cout << "[ICP] Assertion (nonlinear)" << *constr <<  endl;
            cout << "mNonlinearConstraints.size: " << mNonlinearConstraints.size() << endl;
            cout << "Number Candidates: " << mNonlinearConstraints[constr].size() << endl;
            #endif
            for( auto candidateIt = mNonlinearConstraints[constr].begin(); candidateIt != mNonlinearConstraints[constr].end(); ++candidateIt )
            {
                std::map<icp::ContractionCandidate*, unsigned, icp::contractionCandidateComp>::iterator activeCandidateIt = mActiveNonlinearConstraints.find( *candidateIt );
                if( activeCandidateIt != mActiveNonlinearConstraints.end() )
                {
                    (*candidateIt)->addOrigin(*_formula);
                    (*activeCandidateIt).second += 1;
                    #ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Increased candidate count: ";
                    (*candidateIt)->print();
                    #endif
                }
                else
                {
                    (*candidateIt)->addOrigin(*_formula);
                    mActiveNonlinearConstraints[*candidateIt] = 1;
                    #ifdef ICPMODULE_DEBUG
                    cout << "[ICP] Activated candidate: ";
                    (*candidateIt)->print();
                    #endif
                }

                // activate for mIcpRelevantCandidates Management
                (*candidateIt)->activate();
                // update affectedCandidates
                for ( auto varIt = (*candidateIt)->constraint()->variables().begin(); varIt != (*candidateIt)->constraint()->variables().end(); ++varIt )
                {
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "[ICP] Added to affected canndidates: " << (*varIt) << " -> ";
                    (*candidateIt)->print();
                    #endif
                    #endif
                    // try to insert new icpVariable - if already existing, only a candidate is added, else a new icpVariable is created.
                    bool original = !( (*candidateIt)->lhs() == *varIt);
                    icp::IcpVariable* icpVar = NULL;
                    if( original )
                        icpVar = new icp::IcpVariable(*varIt, original , *candidateIt, icp::getOriginalLraVar(*varIt,mLRA));
                    else
                        icpVar = new icp::IcpVariable(*varIt, original , *candidateIt);
                    std::pair<std::map<const carl::Variable, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(*varIt, icpVar));
                    if (!added.second)
                    {
                        (*added.first).second->addCandidate(*candidateIt);
                        delete icpVar;
                    }
                }
            }
        }
        const Formula* replacementPtr = NULL;
        // lookup corresponding linearization - in case the constraint is already linear, mReplacements holds the constraint as the linearized one
        for ( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt )
        {
            if ( *(*replacementIt).second == (**_formula) )
            {
                replacementPtr = (*replacementIt).first;
                break;
            }
        }
        assert(replacementPtr != NULL);
        
        if ( replacementPtr->constraint().isBound() )
        {
            // considered constraint is activated but has no slackvariable -> it is a boundary constraint
            assert(replacementPtr->getType() == CONSTRAINT);
            mValidationFormula->push_back(replacementPtr);
            // update ReceivedFormulaMapping
//            mReceivedFormulaMapping.insert(std::make_pair(replacementPtr, *_formula));
            // try to insert new icpVariable -> is original!
            const carl::Variable::Arg tmpVar = *replacementPtr->constraint().variables().begin();
            const LRAVariable* slackvariable = mLRA.getSlackVariable(replacementPtr->pConstraint());
            assert( slackvariable != NULL );
            icp::IcpVariable* icpVar = new icp::IcpVariable(tmpVar, true, slackvariable );
            std::pair<std::map<const carl::Variable, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(tmpVar, icpVar));
            if (!added.second)
                delete icpVar;
                
            #ifdef ICPMODULE_DEBUG
            cout << "[mLRA] Assert bound constraint: " << *replacementPtr << endl;
            #endif
            if ( !mLRA.assertSubformula(--mValidationFormula->end()) )
            {
                remapAndSetLraInfeasibleSubsets();
                assert(!mInfeasibleSubsets.empty());
                return false;
            }
        }
        else //if ( (*_formula)->constraint().variables().size() > 1 )
        {
            const LRAVariable* slackvariable = mLRA.getSlackVariable(replacementPtr->pConstraint());
            assert(slackvariable != NULL);

            // lookup if contraction candidates already exist - if so, add origins
            bool alreadyExisting = (mLinearConstraints.find(slackvariable) != mLinearConstraints.end());
            if (alreadyExisting)
            {
                for ( auto candidateIt = mLinearConstraints.at(slackvariable).begin(); candidateIt != mLinearConstraints.at(slackvariable).end(); ++candidateIt )
                {
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "[ICP] ContractionCandidates already exist: ";
                    slackvariable->print();
                    cout << ", Size Origins: " << (*candidateIt)->origin().size() << endl;

                    cout << (*_formula) << endl;
                    (*candidateIt)->print();
                    cout << "Adding origin." << endl;
                    #endif
                    #endif
                    // add origin
                    (*candidateIt)->addOrigin(*_formula);

                    // set value in activeLinearConstraints
                    if ( mActiveLinearConstraints.find(*candidateIt) == mActiveLinearConstraints.end() )
                        mActiveLinearConstraints[(*candidateIt)] = 1;
                    else
                        mActiveLinearConstraints[(*candidateIt)] += 1;
                }
            }
            else
            {
                // if not existent:
                Variables variables = replacementPtr->constraint().variables();
                bool hasRealVar = false;
                for( auto var : variables )
                {
                    if( var.getType() == carl::VariableType::VT_REAL )
                    {
                        hasRealVar = true;
                        break;
                    }
                }
                carl::Variable newVar = hasRealVar ? newAuxiliaryRealVariable() : newAuxiliaryIntVariable();
                variables.insert(newVar);

                const Polynomial rhs = slackvariable->expression()-newVar;
                const Constraint* tmpConstr = newConstraint(rhs, Relation::EQ);
               
                // Create candidates for every possible variable:
                for (auto variableIt = variables.begin(); variableIt != variables.end(); ++variableIt )
                {
                    if( mContractors.find(rhs) == mContractors.end() )
                    {
                        mContractors.insert(std::make_pair(rhs, Contractor<carl::SimpleNewton>(rhs)));
                    }
                    icp::ContractionCandidate* newCandidate = mCandidateManager->getInstance()->createCandidate(newVar, rhs, tmpConstr, *variableIt, mContractors.at(rhs),*_formula);

                    // ensure that the created candidate is set as linear
                    newCandidate->setLinear();
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "[ICP] Create & activate candidate: ";
                    newCandidate->print();
                    slackvariable->print();
                    #endif
                    #endif
                    // add to linearConstraints and ActiveLinearConstraints
                    mLinearConstraints[slackvariable].insert(newCandidate);
                    mActiveLinearConstraints[newCandidate] = 1;

                    // set interval to unbounded if not existing - we need an interval for the icpVariable
                    if ( mIntervals.find(newVar) == mIntervals.end() )
                    {
                        mIntervals.insert(std::make_pair(newVar, smtrat::DoubleInterval::unboundedInterval()));
                        mHistoryRoot->addInterval(newVar, smtrat::DoubleInterval::unboundedInterval());
                    }
                   
                    // try to add icpVariable - if already existing, only add the created candidate, else create new icpVariable
                    bool original = (*variableIt != newVar);
                    icp::IcpVariable* icpVar = NULL;
                    if( original )
                        icpVar = new icp::IcpVariable(*variableIt, original, newCandidate, icp::getOriginalLraVar(*variableIt,mLRA) );
                    else
                        icpVar = new icp::IcpVariable(*variableIt, original, newCandidate, slackvariable );
                    std::pair<std::map<const carl::Variable, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(*variableIt, icpVar));
                    if(!added.second)
                    {
                        (*added.first).second->addCandidate(newCandidate);
                        if ((*added.first).second->isOriginal())
                                (*added.first).second->setLraVar(icp::getOriginalLraVar(*variableIt,mLRA));
                            else
                                (*added.first).second->setLraVar(slackvariable);
                        delete icpVar;
                    }
                   
                    // update affectedCandidates
                    for ( auto varIt = variables.begin(); varIt != variables.end(); ++varIt )
                    {
                        original = (*_formula)->pConstraint()->hasVariable(*varIt);
                        icp::IcpVariable* icpVar = NULL;
                        if( original )
                            icpVar = new icp::IcpVariable(*varIt, original, newCandidate, icp::getOriginalLraVar(*varIt,mLRA) );
                        else
                            icpVar = new icp::IcpVariable(*varIt, original, newCandidate, slackvariable );      
                        std::pair<std::map<const carl::Variable, icp::IcpVariable*>::iterator,bool> added = mVariables.insert(std::make_pair(*varIt, icpVar));
                        if(!added.second)
                        {
                            (*added.first).second->addCandidate(newCandidate);
                            if ((*added.first).second->isOriginal())
                                (*added.first).second->setLraVar(icp::getOriginalLraVar(*varIt,mLRA));
                            else
                                (*added.first).second->setLraVar(slackvariable);
                            delete icpVar;
                        }
                        #ifdef ICPMODULE_DEBUG
                        #ifndef ICPMODULE_REDUCED_DEBUG
                        cout << "[ICP] Added to affected canndidates: " << *varIt << " -> ";
                        newCandidate->print();
                        #endif
                        #endif
                    }
                }
            }

            // assert in mLRA
            assert(replacementPtr != NULL);
            assert(replacementPtr->getType() == CONSTRAINT);
            mValidationFormula->push_back(replacementPtr);

            // update ReceivedFormulaMapping
//            mReceivedFormulaMapping.insert(std::make_pair(replacementPtr, *_formula));
            
            if( !mLRA.assertSubformula(--mValidationFormula->end()) )
            {
                remapAndSetLraInfeasibleSubsets();
                return false;
            }
            #ifdef ICPMODULE_DEBUG
            cout << "[mLRA] Assert " << *replacementPtr << endl;
            #endif
        }
        return true;
    }


    void ICPModule::removeSubformula( ModuleInput::const_iterator _formula )
    {
        const Constraint* constr = (*_formula)->pConstraint();
        #ifdef ICPMODULE_DEBUG
        cout << "[ICP] Remove Formula " << *constr << endl;
        #endif
        // is it nonlinear?
        if (mNonlinearConstraints.find(constr) != mNonlinearConstraints.end())
        {
            #ifdef ICPMODULE_DEBUG
            cout << "Nonlinear." << endl;
            #endif
            set<icp::ContractionCandidate*>::iterator candidateIt;
            assert( mNonlinearConstraints.find(constr) != mNonlinearConstraints.end() );
            
            std::map<string, icp::IcpVariable*>::iterator toRemove;
            for( candidateIt = mNonlinearConstraints.at(constr).begin(); candidateIt != mNonlinearConstraints.at(constr).end(); ++candidateIt )
            {
                // remove origin, no matter if constraint is active or not
                (*candidateIt)->removeOrigin(*_formula);
                
                //store slackvariable for later removal.
//                toRemove = mVariables.find((*candidateIt)->lhs().get_name());
//                assert(toRemove != mVariables.end());

                // remove candidate if counter == 1, else decrement counter.
                if( mActiveNonlinearConstraints.find( *candidateIt ) != mActiveNonlinearConstraints.end() )
                {
                    if( mActiveNonlinearConstraints.at(*candidateIt) > 1 )
                    {
                        mActiveNonlinearConstraints[*candidateIt] = mActiveNonlinearConstraints.at(*candidateIt) - 1;

                        // directly decrement linear replacements
                        for ( auto activeLinearIt = mActiveLinearConstraints.begin(); activeLinearIt != mActiveLinearConstraints.end(); ++activeLinearIt )
                        {
                            if ( (*activeLinearIt).first->hasOrigin(*_formula) )
                            {
                                #ifdef ICPMODULE_DEBUG
                                #ifndef ICPMODULE_REDUCED_DEBUG
                                cout << "Remove linear origin from candidate " << (*activeLinearIt).first->id() << endl;
                                #endif
                                #endif
                                (*activeLinearIt).first->removeOrigin(*_formula);
                                if ( (*activeLinearIt).second > 1 )
                                {
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Decrease counter." << endl;
                                    #endif
                                    #endif
                                    mActiveLinearConstraints[(*activeLinearIt).first]--;
                                }
                                else
                                {
                                    // reset History to point before this candidate was used
                                    icp::HistoryNode::set_HistoryNode nodes =  mHistoryRoot->findCandidates((*activeLinearIt).first);
                                    // as the set is sorted ascending by id, we pick the node with the lowest id
                                    if ( !nodes.empty() )
                                    {
                                        icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                                        if ( *firstNode == *mHistoryRoot )
                                        {
                                            firstNode = mHistoryRoot->addRight(new icp::HistoryNode(mHistoryRoot->intervals(), 2));
                                        }
                                        setBox(firstNode);
                                        mHistoryActual->reset();
                                    }
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Erase candidate from active." << endl;
                                    #endif
                                    #endif
                                    // clean up icpRelevantCandidates
                                    removeCandidateFromRelevant((*activeLinearIt).first);
                                    (*activeLinearIt).first->deactivate();
                                    mActiveLinearConstraints.erase((*activeLinearIt).first);
                                }
                            }
                        }
                    }
                    // total removal
                    else if( mActiveNonlinearConstraints[*candidateIt] == 1 )
                    {
                        // reset History to point before this candidate was used
                        icp::HistoryNode::set_HistoryNode nodes =  mHistoryRoot->findCandidates(*candidateIt);
                        // as the set is sorted ascending by id, we pick the node with the lowest id
                        if ( !nodes.empty() )
                        {
                            icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                            if ( *firstNode == *mHistoryRoot )
                                firstNode = mHistoryRoot->addRight(new icp::HistoryNode(mHistoryRoot->intervals(), 2));
                            
                            setBox(firstNode);
                            mHistoryActual->reset();
                        }
                        // clean up icpRelevantCandidates
                        removeCandidateFromRelevant((*candidateIt));
                        (*candidateIt)->deactivate();
                        mActiveNonlinearConstraints.erase( *candidateIt );
                    }
                }

                // a total removal has happened -> erase all related information (cleanup)
                if (mActiveNonlinearConstraints.find(*candidateIt) == mActiveNonlinearConstraints.end())
                {
                    // clean up affected candidates
                    for ( auto variableIt = (*candidateIt)->constraint()->variables().begin(); variableIt != (*candidateIt)->constraint()->variables().end(); ++variableIt )
                    {
                        std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
                        assert(icpVar != mVariables.end());
                        for ( auto varCandidateIt = (*icpVar).second->candidates().begin(); varCandidateIt != (*icpVar).second->candidates().end(); )
                        {
                            if ( *candidateIt == *varCandidateIt )
                                varCandidateIt = (*icpVar).second->candidates().erase(varCandidateIt);
                            else
                                ++varCandidateIt;
                        }
                    }

                    // find all linear replacements and deactivate them as well
                    for ( auto activeLinearIt = mActiveLinearConstraints.begin(); activeLinearIt != mActiveLinearConstraints.end(); )
                    {
                        if ( (*activeLinearIt).first->hasOrigin(*_formula) )
                        {
                            if ( (*activeLinearIt).second > 1 )
                            {
                                //This should not happen
                                assert(false);
                            }
                            else
                            {
                                // clean up affected candidates before deletion
                                for( auto variablesIt = constr->variables().begin(); variablesIt != constr->variables().end(); ++variablesIt )
                                {
                                    std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variablesIt);
                                    (*icpVar).second->deleteCandidate((*activeLinearIt).first);
                                }
                                // clean up icpRelevantCandidates
                                removeCandidateFromRelevant((*activeLinearIt).first);
                                (*activeLinearIt).first->deactivate();
                                #ifdef ICPMODULE_DEBUG
                                #ifndef ICPMODULE_REDUCED_DEBUG                                
                                cout << "deactivate." << endl;
                                #endif
                                #endif
                                activeLinearIt= mActiveLinearConstraints.erase(activeLinearIt);
                            }
                        }
                        else
                            ++activeLinearIt;
                    }
                }
            }
//            mVariables.erase(toRemove);
        }

        // linear handling
        bool mLraCleared = false;
        std::map<unsigned, icp::ContractionCandidate*> candidates = mCandidateManager->getInstance()->rCandidates();
        for ( auto candidateIt = candidates.begin(); candidateIt != candidates.end(); ++candidateIt )
        {
            if ( (*candidateIt).second->isLinear() && (*candidateIt).second->hasOrigin(*_formula) )
            {
                #ifdef ICPMODULE_DEBUG
                #ifndef ICPMODULE_REDUCED_DEBUG
                cout << "Found linear candidate: ";
                (*candidateIt).second->print();
                cout << endl;
                #endif
                #endif
                (*candidateIt).second->removeOrigin(*_formula);
                if (!mLraCleared)
                {
                    for ( auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); )
                    {
                        if ( (*formulaIt)->constraint() == (*_formula)->constraint() )
                        {
                            mLraCleared = true;
                            #ifdef ICPMODULE_DEBUG
                            cout << "[mLRA] Remove constraint: " << (*_formula)->constraint() << endl;
                            #endif
                            mLRA.removeSubformula(formulaIt);
//                            mReceivedFormulaMapping.erase(*formulaIt);
                            formulaIt = mValidationFormula->erase(formulaIt);
                            break;
                        }
                        else
                            ++formulaIt;
                    }
                }

                if( mActiveLinearConstraints.find( (*candidateIt).second ) != mActiveLinearConstraints.end() )
                {
                    if( mActiveLinearConstraints[(*candidateIt).second] > 1 )
                    {
                        mActiveLinearConstraints[(*candidateIt).second] = mActiveLinearConstraints[(*candidateIt).second] - 1;
                        // no need to remove in mLRA since counter >= 1
                    }
                    else
                    {
                        // reset History to point before this candidate was used
                        icp::HistoryNode::set_HistoryNode nodes =  mHistoryRoot->findCandidates((*candidateIt).second);
                        // as the set is sorted ascending by id, we pick the node with the lowest id
                        if ( !nodes.empty() )
                        {
                            icp::HistoryNode* firstNode = (*nodes.begin())->parent();
                            if ( *firstNode == *mHistoryRoot )
                                firstNode = mHistoryRoot->addRight(new icp::HistoryNode(mHistoryRoot->intervals(), 2));
                            
                            setBox(firstNode);
                            mHistoryActual->reset();
                        }
                        // clean up icpRelevantCandidates
                        removeCandidateFromRelevant((*candidateIt).second);
                        (*candidateIt).second->deactivate();
                        mActiveLinearConstraints.erase( (*candidateIt).second );
                    }
                }
            }
        }
        // remove constraint from mLRA module -> is identified by replacements-map Todo: IMPROVE, maybe we can avoid replacements mapping
        for ( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt )
        {
            if ( (**_formula) == *(*replacementIt).second)
            {
                for ( auto validationFormulaIt = mValidationFormula->begin(); validationFormulaIt != mValidationFormula->end(); ++validationFormulaIt )
                {
                    if ( (**validationFormulaIt) == *(*replacementIt).first )
                    {
                        #ifdef ICPMODULE_DEBUG
                        cout << "[mLRA] remove " << *(*validationFormulaIt)->pConstraint() << endl;
                        #endif
                        mLRA.removeSubformula(validationFormulaIt);
//                        mReceivedFormulaMapping.erase(*validationFormulaIt);
                        mValidationFormula->erase(validationFormulaIt);
                        break;
                    }
                }
                break;
            }
        }
        
        Module::removeSubformula( _formula );
    }


    Answer ICPModule::isConsistent()
    {
        // Dirty! Normally this shouldn't be neccessary
        mInfeasibleSubsets.clear();
        mIsBackendCalled = false;
        double relativeContraction = 1;
        double absoluteContraction = 0;
        bool   splitOccurred = false;
        std::pair<bool,carl::Variable> didSplit = std::make_pair(false, carl::Variable::NO_VARIABLE);
        vec_set_const_pFormula violatedConstraints = vec_set_const_pFormula();
        double contractionThreshold = 0.001;

        // Debug Outputs of linear and nonlinear Tables
        #ifdef ICPMODULE_DEBUG
        debugPrint();
        printAffectedCandidates();
        printIcpVariables();
        cout << "Id selected box: " << mHistoryRoot->id() << " Size subtree: " << mHistoryRoot->sizeSubtree() << endl;
        #endif
        // call mLRA to check linear feasibility
        mLRA.clearDeductions();
        mLRA.rReceivedFormula().updateProperties();
        Answer lraAnswer = mLRA.isConsistent();
        
        // catch deductions
        mLRA.updateDeductions();
        while( !mLRA.deductions().empty() )
        {
            #ifdef ICPMODULE_DEBUG
            #ifndef ICPMODULE_REDUCED_DEBUG
            cout << "Create deduction for: " << *mLRA.deductions().back() << endl;
            #endif
            #endif
            const Formula* deduction = transformDeductions(mLRA.deductions().back());
            mLRA.rDeductions().pop_back();
            addDeduction(deduction);
            #ifdef ICPMODULE_DEBUG
            #ifndef ICPMODULE_REDUCED_DEBUG            
            cout << "Passed deduction: " << *deduction << endl;
            #endif
            #endif
        }
        
        mLRA.clearDeductions();
        
        if (lraAnswer == False)
        {
            // remap infeasible subsets to original constraints
            remapAndSetLraInfeasibleSubsets();
            #ifdef ICPMODULE_DEBUG
            cout << "LRA: " << lraAnswer << endl;
            #endif
            return foundAnswer(lraAnswer);
        }
        else if ( lraAnswer == Unknown)
        {
            #ifdef ICPMODULE_DEBUG
            mLRA.printReceivedFormula();
            cout << "LRA: " << lraAnswer << endl;
            #endif
            return foundAnswer(lraAnswer);
        }
        else if ( !mActiveNonlinearConstraints.empty() ) // lraAnswer == True
        {
            // get intervals for initial variables
            EvalIntervalMap tmp = mLRA.getVariableBounds();
            #ifdef ICPMODULE_DEBUG
            cout << "Newly obtained Intervals: " << endl;
            #endif
            for ( auto constraintIt = tmp.begin(); constraintIt != tmp.end(); ++constraintIt )
            {
                #ifdef ICPMODULE_DEBUG
                cout << (*constraintIt).first << ": " << (*constraintIt).second << endl;
                #endif
                if (mVariables.find((*constraintIt).first) != mVariables.end())
                {
                    Interval tmp = (*constraintIt).second;
                    mHistoryRoot->addInterval((*constraintIt).first, smtrat::DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType()) );
                    mIntervals[(*constraintIt).first] = smtrat::DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType() );
                    mVariables.at((*constraintIt).first)->setUpdated();
                }
            }
            
            // get intervals for slackvariables
            const LRAModule::ExVariableMap slackVariables = mLRA.slackVariables();
            for ( auto slackIt = slackVariables.begin(); slackIt != slackVariables.end(); ++slackIt )
            {
                std::map<const LRAVariable*, ContractionCandidates>::iterator linIt = mLinearConstraints.find((*slackIt).second);
                if ( linIt != mLinearConstraints.end() )
                {
                    // dirty hack: expect lhs to be set and take first item of set of CCs --> Todo: Check if it is really set in the constructors of the CCs during inform and assert
                    Interval tmp = (*slackIt).second->getVariableBounds();
                    // keep root updated about the initial box.
                    mHistoryRoot->rIntervals()[(*(*linIt).second.begin())->lhs()] = smtrat::DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType());
                    mIntervals[(*(*linIt).second.begin())->lhs()] = smtrat::DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType());
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "Added interval (slackvariables): " << (*(*linIt).second.begin())->lhs() << " " << tmp << endl;
                    #endif
                    #endif
                }
            }
            // temporary solution - an added linear constraint might have changed the box.
            setBox(mHistoryRoot);
            mHistoryRoot->rReasons().clear();
            mHistoryRoot->rStateInfeasibleConstraints().clear();
            mHistoryRoot->rStateInfeasibleVariables().clear();
            mHistoryActual = mHistoryActual->addRight(new icp::HistoryNode(mIntervals,2));
            mCurrentId = mHistoryActual->id();
            #ifdef ICPMODULE_DEBUG
            cout << "Id actual box: " << mHistoryActual->id() << " Size subtree: " << mHistoryActual->sizeSubtree() << endl;
            #endif
        }
        else if ( mActiveNonlinearConstraints.empty() ) // lraAnswer == True, but no nonlinear constraints -> nothing to do
        {
#ifdef ICPMODULE_DEBUG
            cout << "LRA: " << lraAnswer << endl;
#endif
            return foundAnswer(lraAnswer);
        }
            

        bool boxFeasible = true;
        bool invalidBox = false;

        #ifdef ICP_BOXLOG
        icpLog << "startTheoryCall";
        writeBox();
        #endif
        
#ifdef ICPMODULE_DEBUG
        printIntervals(true);
        cout << "---------------------------------------------" << endl;
#endif
        
        do //while BoxFeasible
        {
            bool icpFeasible = true;
            mLastCandidate = NULL;

            while ( icpFeasible )
            {
                #ifndef BOXMANAGEMENT
                while(!mBoxStorage.empty())
                    mBoxStorage.pop();
                
                icp::set_icpVariable icpVariables;
                Variables originalRealVariables;
                mpReceivedFormula->realValuedVars(originalRealVariables);
                for( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
                {
                    assert(mVariables.count(*variablesIt) > 0);
                    icpVariables.insert( (*(mVariables.find(*variablesIt))).second );
                }
                PointerSet<Formula> box = variableReasonHull(icpVariables);
                mBoxStorage.push(box);
//                cout << "ADD TO BOX!" << endl;
                #endif
                #ifdef ICPMODULE_DEBUG
                cout << "********************** [ICP] Contraction **********************" << endl;
                cout << "Subtree size: " << mHistoryRoot->sizeSubtree() << endl;
                mHistoryActual->print();
                #endif
                #ifdef ICP_BOXLOG
                icpLog << "startContraction";
                writeBox();
                #endif
                #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                Formula* negatedContraction = new Formula(*mpReceivedFormula);
                GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                    tmp.insert((*constraintIt));
                
                std::vector<Formula*> boundaryConstraints = createConstraintsFromBounds(tmp);
                for ( auto boundaryConstraint = boundaryConstraints.begin(); boundaryConstraint != boundaryConstraints.end(); ++boundaryConstraint )
                    negatedContraction->addSubformula(*boundaryConstraint);
                #endif
                // prepare IcpRelevantCandidates
                activateLinearEquations();
                fillCandidates();
                splitOccurred = false;
                
                while ( !mIcpRelevantCandidates.empty() && !splitOccurred )
                {
                    
                    #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                    mCheckContraction = new Formula(*mpReceivedFormula);
                    
                    GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                    for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                        tmp.insert((*constraintIt));
                    
                    std::vector<Formula*> boundaryConstraints = createConstraintsFromBounds(tmp);
                    for ( auto boundaryConstraint = boundaryConstraints.begin(); boundaryConstraint != boundaryConstraints.end(); ++boundaryConstraint )
                        mCheckContraction->addSubformula(*boundaryConstraint);
                    #endif
                    
                    icp::ContractionCandidate* candidate = chooseContractionCandidate();
                    assert(candidate != NULL);
                    candidate->calcDerivative();
                    relativeContraction = -1;
                    absoluteContraction = 0;
                    splitOccurred = contraction( candidate, relativeContraction, absoluteContraction );
                    #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                    if ( !splitOccurred && relativeContraction != 0 )
                    {
                        GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                        for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                            tmp.insert((*constraintIt));
                        
                        std::vector<Formula*> contractedBox = createConstraintsFromBounds(tmp);
                        Formula* negBox = new Formula(NOT);
                        Formula* boxConjunction = new Formula(AND);
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
                        #ifdef ICPMODULE_DEBUG
                        cout << "GENERATED EMPTY INTERVAL, Drop Box: " << endl;
                        #endif
                        mLastCandidate = candidate;
                        invalidBox = true;
                        break;
                    }
                    
                    if ( relativeContraction > 0 )
                    {
                        std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(candidate->derivationVar());
                        assert(icpVar != mVariables.end());
                        (*icpVar).second->setUpdated();
                        mLastCandidate = candidate;
                    }

                    // update weight of the candidate
                    removeCandidateFromRelevant(candidate);
                    candidate->setPayoff(relativeContraction);
                    candidate->calcRWA();

                    // only add nonlinear CCs as linear CCs should only be used once
                    if ( !candidate->isLinear() )
                        addCandidateToRelevant(candidate);
                    
                    assert(mIntervals.find(candidate->derivationVar()) != mIntervals.end() );
#ifdef ICP_CONSIDER_WIDTH
                    if ( (relativeContraction < contractionThreshold && !splitOccurred)  || mIntervals.at(candidate->derivationVar()).diameter() <= mTargetDiameter )
#else
                    if ( (absoluteContraction < contractionThreshold && !splitOccurred) )
#endif
                        removeCandidateFromRelevant(candidate);
#ifdef ICP_CONSIDER_WIDTH
                    else if ( relativeContraction >= contractionThreshold )
#else
                    else if ( absoluteContraction >= contractionThreshold )
#endif
                    {
                        /**
                         * make sure all candidates which contain the variable
                         * of which the interval has significantly changed are
                         * contained in mIcpRelevantCandidates.
                         */
                        std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(candidate->derivationVar());
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
                                addCandidateToRelevant(*candidateIt);
                        }
                        #ifdef ICP_BOXLOG
                        icpLog << "contraction; \n";
                        #endif
                    }
                    
#ifdef ICP_CONSIDER_WIDTH
                    bool originalAllFinished = true;
                    Variables originalRealVariables;
                    mpReceivedFormula->realValuedVars(originalRealVariables);
                    for ( auto varIt = originalRealVariables.begin(); varIt != originalRealVariables.end(); ++varIt )
                    {
                        if ( mIntervals.find(*varIt) != mIntervals.end() )
                        {
                            if ( mIntervals.at(*varIt).diameter() > mTargetDiameter )
                            {
                                originalAllFinished = false;
                                break;
                            }
                        }
                    }
                    if ( originalAllFinished )
                    {
                        mIcpRelevantCandidates.clear();
                        break;
                    }
#endif
                } //while ( !mIcpRelevantCandidates.empty() && !splitOccurred)
                // do not verify if the box is already invalid
                if (!invalidBox && !splitOccurred)
                {
                    invalidBox = !checkBoxAgainstLinearFeasibleRegion();
                    #ifdef ICPMODULE_DEBUG
                    cout << "Invalid against linear region: " << invalidBox << endl;
                    #endif
                    #ifdef ICP_BOXLOG
                    if ( invalidBox )
                    {
                        icpLog << "invalid Post Contraction; \n";
                    }
                    #endif
                    // do a quick test with one point.
//                    if( !invalidBox )
//                    {
//                        EvalRationalMap rationals;
//                        std::map<carl::Variable, double> values = createModel();
//                        for(auto value : values)
//                        {
//                            rationals.insert(std::make_pair(value.first, carl::rationalize<Rational>(value.second)));
//                        }
//                        unsigned result = mpReceivedFormula->satisfiedBy(rationals);
//                        if ( result == 1 )
//                        {
//                            return foundAnswer(True);
//                        }
//                    }
                }
                #ifdef ICP_BOXLOG
                else
                {
                    icpLog << "contract to emp; \n";
                }
                #endif
                #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                if ( !splitOccurred && !invalidBox )
                {
                    GiNaCRA::evaldoubleintervalmap tmp = GiNaCRA::evaldoubleintervalmap();
                    for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
                        tmp.insert((*constraintIt));
                    
                    std::vector<Formula*> contractedBox = createConstraintsFromBounds(tmp);
                    Formula* negConstraint = new Formula(NOT);
                    Formula* conjunction = new Formula(AND);
                    for ( auto formulaIt = contractedBox.begin(); formulaIt != contractedBox.end(); ++formulaIt )
                        conjunction->addSubformula(*formulaIt);

                    negConstraint->addSubformula(conjunction);
                    negatedContraction->addSubformula(negConstraint);
                    addAssumptionToCheck(*negatedContraction,false,"ICPContractionCheck");
                }
                negatedContraction->clear();
                delete negatedContraction;
                #endif
                didSplit.first = false;
                if(invalidBox || splitOccurred ||mIcpRelevantCandidates.empty()) // relevantCandidates is not empty, if we got new bounds from LRA during boxCheck
                {
                    // perform splitting if possible
                    if ( !invalidBox && !splitOccurred )
                    {
                        didSplit = checkAndPerformSplit();
                    }
      
                    if ( didSplit.first || (splitOccurred && !invalidBox) )
                    {
                        #ifdef ICP_BOXLOG
                        icpLog << "split size subtree; " << mHistoryRoot->sizeSubtree() << "\n";
                        #endif
                        #ifdef ICPMODULE_DEBUG
                        #ifndef ICPMODULE_REDUCED_DEBUG
                        cout << "Size subtree: " << mHistoryActual->sizeSubtree() << " \t Size total: " << mHistoryRoot->sizeSubtree() << endl;
                        #endif
                        #endif
                        #ifndef BOXMANAGEMENT
                        #ifdef ICPMODULE_DEBUG
                        cout << "Return unknown, raise deductions for split." << endl;
                        #endif
                        return foundAnswer(Unknown);
                        #endif
                        invalidBox = false;
                        icpFeasible = true;
                    }
                    else
                        icpFeasible = false;

                    #ifdef ICPMODULE_DEBUG
                    cout << "empty: " << invalidBox << "  didSplit: " << didSplit.first << endl;
                    #endif
                }
            } //while ( icpFeasible )

            // when one interval is empty, we can skip validation and chose next box.
            if ( !invalidBox )
            {
                //call validation
                std::pair<bool,bool> validationResult = validateSolution();
                bool newConstraintAdded = validationResult.first;
                bool boxValidated = validationResult.second;

                if(!boxValidated)
                {
                    #ifdef ICP_BOXLOG
                    icpLog << "invalid Post Validation; \n";
                    #endif
                    // choose & set new box
                    #ifdef BOXMANAGEMENT
                    #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
                    Module::addAssumptionToCheck(mLRA.rReceivedFormula(),false,"ICP_CenterpointValidation");
                    #endif
                    #ifdef ICPMODULE_DEBUG
                    cout << "Box not Validated, Chose new box: " << endl;
                    #endif
                    // set stateInfeasibleSubset
//                    cout << "[Post-Validate]" << endl;
//                    for (auto infSetIt = (*mInfeasibleSubsets.begin()).begin(); infSetIt != (*mInfeasibleSubsets.begin()).end(); ++infSetIt )
//                        mHistoryActual->addInfeasibleConstraint((*infSetIt)->pConstraint());
                    
                    mLastCandidate = NULL;
                    icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                    if ( newBox != NULL )
                        setBox(newBox);
                    else
                    {
                        // no new Box to select -> finished
                        boxFeasible = false;

                        //TODO: If chooseBox worked properly, this wouldn't be necessary.
                        mHistoryActual->propagateStateInfeasibleConstraints();
                        mHistoryActual->propagateStateInfeasibleVariables();
                        
                        mInfeasibleSubsets.clear();
                        mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
//                        printInfeasibleSubsets();
                        return foundAnswer(False);
                    }
                    #else
                    mInfeasibleSubsets.push_back(createPremiseDeductions());
                    return Unknown;
                    #endif
                }
                else if (!newConstraintAdded)
                {
                    /**
                    * If no change has happened after the validation the set was either empty
                    * or we didn't add new constraints which results in a direct acceptance of
                    * the solution (Why? -> numerical errors)
                    */
                    // create Bounds and set them, add to passedFormula
                    bool boxChanged = pushBoundsToPassedFormula();
                    // remove centerConstaints as soon as they are not longer needed.
                    clearCenterConstraintsFromValidationFormula();
                    
                    if ( boxChanged )
                    {
                        #ifdef ICPMODULE_DEBUG
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
                        #ifdef ICPMODULE_DEBUG
                        cout << "[ICP] Done running backends:" << a << endl;
                        #endif
                        if( a == False )
                        {
                            assert(infeasibleSubsets().empty());
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
                                        std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.begin();
                                        for ( ; icpVar != mVariables.end(); ++icpVar )
                                        {
                                            if( (*icpVar).second->isOriginal() && (*icpVar).second->isExternalBoundsSet() != icp::Updated::NONE )
                                            {
                                                assert( (*icpVar).second->isExternalUpdated() != icp::Updated::NONE );
                                                if ( (*subformula) == (*(*icpVar).second->externalLeftBound()) || (*subformula) == (*(*icpVar).second->externalRightBound()) )
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
                                                PointerSet<Formula> infeasibleSubset;
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
                                #ifdef BOXMANAGEMENT
                                #ifdef ICPMODULE_DEBUG
                                cout << "InfSet of Backend contained bound, Chose new box: " << endl;
                                #endif
                                mLastCandidate = NULL;
                                icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                                if ( newBox != NULL )
                                    setBox(newBox);
                                else
                                {
                                    #ifdef ICPMODULE_DEBUG
                                    cout << "No new box found. Return false." << endl;
                                    #endif
                                    //TODO: If chooseBox would work properly, this wouldn't be necessary
                                    mHistoryActual->propagateStateInfeasibleConstraints();
                                    mHistoryActual->propagateStateInfeasibleVariables();
                                    // no new Box to select -> finished
                                    mInfeasibleSubsets.clear();
                                    mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
//                                    printInfeasibleSubsets();
                                    return foundAnswer(False);
                                }
                                #else
                                mInfeasibleSubsets.push_back(createPremiseDeductions());
                                return foundAnswer(Unknown);
                                #endif
                            }
                            else
                            {
                                mHistoryActual->propagateStateInfeasibleConstraints();
                                mHistoryActual->propagateStateInfeasibleVariables();
                                mInfeasibleSubsets.clear();
                                mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
//                                printInfeasibleSubsets();
                                return foundAnswer(False);
                            }
                        }
                        else // if answer == true or answer == unknown
                        {
                            mHistoryActual->propagateStateInfeasibleConstraints();
                            mHistoryActual->propagateStateInfeasibleVariables();
#ifdef ICPMODULE_DEBUG
                            cout << "Backend: " << a << endl;
#endif
                            return foundAnswer(a);
                        }
                    }
                    else // Box hasn't changed
                    {
                        #ifdef BOXMANAGEMENT
                        #ifdef ICPMODULE_DEBUG
                        cout << "Box hasn't changed, Chose new box: " << endl;
                        #endif
                        // we do not need to propagate the stateInfeasibleSet, as the box didn't change also this set has been set somewhere before.
//                        for( auto constraintIt = mHistoryActual->reasons().at(mLastCandidate->lhs().get_name()).begin(); constraintIt != mHistoryActual->reasons().at(mLastCandidate->lhs().get_name()).end(); ++constraintIt )
//                            mHistoryActual->addInfeasibleConstraint(*constraintIt);
//                        
//                        cout << "[No-Box-Change]" << endl;
                        mLastCandidate = NULL;
                        icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                        if ( newBox != NULL )
                            setBox(newBox);
                        else
                        {
                            #ifdef ICPMODULE_DEBUG
                            cout << "No new box found. Return false." << endl;
                            #endif
                            // no new Box to select -> finished
                            //TODO: If chooseBox would work properly, this wouldn't be necessary
                            mHistoryActual->propagateStateInfeasibleConstraints();
                            mHistoryActual->propagateStateInfeasibleVariables();
                            mInfeasibleSubsets.clear();
                            mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
//                            printInfeasibleSubsets();
                            return foundAnswer(False);
                        }
                        #else
                        mInfeasibleSubsets.push_back(createPremiseDeductions());
                        return foundAnswer(Unknown);
                        #endif
                    }
                }
                else // valid Box, newConstraintAdded
                {
                    // do nothing, the resetting of the tree has already been performed in validate
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG                    
                    cout << "Id actual box: " << mHistoryActual->id() << " Size subtree: " << mHistoryActual->sizeSubtree() << endl;
                    #endif
                    #endif
                    #ifdef ICP_BOXLOG
                    icpLog << "validation added new constraints; \n";
                    #endif
                }
                clearCenterConstraintsFromValidationFormula();
            }
            else // if invalidBox -> ChooseNextBox
            {
                #ifdef BOXMANAGEMENT
                #ifdef ICPMODULE_DEBUG
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
//                mHistoryActual->print();
//                mHistoryActual->printReasons();
//                mHistoryActual->printVariableReasons();
                mLastCandidate = NULL;
                icp::HistoryNode* newBox = chooseBox( mHistoryActual );
                if ( newBox != NULL )
                {
                    setBox(newBox);
                    invalidBox = false;
                }
                else
                {
                    #ifdef ICPMODULE_DEBUG
                    cout << "No new box found. Return false." << endl;
                    #endif
                    // no new Box to select -> finished
                    mHistoryActual->propagateStateInfeasibleConstraints();
                    mHistoryActual->propagateStateInfeasibleVariables();
                    mInfeasibleSubsets.clear();
                    mInfeasibleSubsets.push_back(collectReasons(mHistoryRoot));
//                    printInfeasibleSubsets();
                    return foundAnswer(False);
                }
                #else
                mInfeasibleSubsets.push_back(createPremiseDeductions());
                return foundAnswer(False);
                #endif
            }
        }while ( boxFeasible );
        // This should not happen!
        assert(false);
        return foundAnswer(Unknown);
    }
    
    
    Polynomial ICPModule::createContractionCandidates(FastMap<Polynomial, const Constraint*>& _tempMonomes)
    {
        Polynomial linearizedConstraint = Polynomial();
        if( !_tempMonomes.empty() )
        {
            const Constraint* constraint = (*_tempMonomes.begin()).second;
//            Variables substitutions;
            
//            cout << "Constraint: " << *constraint << endl;

            // Create contraction candidate object for every possible derivation variable
            for( auto expressionIt = _tempMonomes.begin(); expressionIt != _tempMonomes.end(); )
            {
                if( mLinearizations.find((*expressionIt).first) == mLinearizations.end() )
                {
                    assert( (*expressionIt).second == constraint );
                    // cCreate mLinearzations entry
                    Variables variables;
                    (*expressionIt).first.gatherVariables(variables);
                    bool hasRealVar = false;
                    for( auto var : variables )
                    {
                        if( var.getType() == carl::VariableType::VT_REAL )
                        {
                            hasRealVar = true;
                            break;
                        }
                    }
                    carl::Variable newVar = hasRealVar ? newAuxiliaryRealVariable() : newAuxiliaryIntVariable();
                    mLinearizations.insert( std::make_pair((*expressionIt).first, newVar) );
                    //mLinearizations[(*expressionIt).first] = newReal;
                    //mSubstitutions[newReal] = (*expressionIt).first;
                    mSubstitutions.insert(std::make_pair(newVar, (*expressionIt).first));
                    //substitutions.insert(std::make_pair((*expressionIt).first, newReal));
                    #ifdef ICPMODULE_DEBUG
                    cout << "New replacement: " << (*expressionIt).first << " -> " << mLinearizations.at((*expressionIt).first) << endl;
                    #endif
                   
                    const Polynomial rhs = (*expressionIt).first-newVar;
                    for( auto varIndex = variables.begin(); varIndex != variables.end(); ++varIndex )
                    {
                        
                        if( mContractors.find(rhs) == mContractors.end() )
                        {
                            mContractors.insert(std::make_pair(rhs, Contractor<carl::SimpleNewton>(rhs)));
                        }
                        const Constraint* tmp = newConstraint( rhs, Relation::EQ);
                        icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(newVar, rhs, tmp, *varIndex, mContractors.at(rhs));
                        mNonlinearConstraints[(*expressionIt).second].insert( mNonlinearConstraints[(*expressionIt).second].end(), tmpCandidate );

                        mIntervals.insert(std::make_pair(*varIndex, smtrat::DoubleInterval::unboundedInterval()));
                        tmpCandidate->activate();
                        tmpCandidate->setNonlinear();
                    }
                    // add one candidate for the replacement variable
                    const Constraint* tmp = newConstraint( (*expressionIt).first-newVar, Relation::EQ);
                    icp::ContractionCandidate* tmpCandidate = mCandidateManager->getInstance()->createCandidate(newVar, rhs, tmp, newVar, mContractors.at(rhs) );
                    mNonlinearConstraints[(*expressionIt).second].insert( mNonlinearConstraints[(*expressionIt).second].end(), tmpCandidate );

                    mIntervals.insert(std::make_pair(newVar, smtrat::DoubleInterval::unboundedInterval()));
                    tmpCandidate->activate();
                    tmpCandidate->setNonlinear();
                }
                else // already existing replacement/substitution/linearization
                {
                    #ifdef ICPMODULE_DEBUG
                    #ifndef ICPMODULE_REDUCED_DEBUG
                    cout << "Existing replacement: " << (*expressionIt).first << " -> " << mLinearizations.at((*expressionIt).first) << endl;
                    #endif
                    #endif
                    for ( auto constraintIt = mNonlinearConstraints.begin(); constraintIt != mNonlinearConstraints.end(); ++constraintIt )
                    {
                        ContractionCandidates tmpList = (*constraintIt).second;
                        for ( auto candidateIt = tmpList.begin(); candidateIt != tmpList.end(); ++candidateIt )
                        {
                            if ( (*candidateIt)->lhs() == mLinearizations.at((*expressionIt).first) )
                                mNonlinearConstraints[(*expressionIt).second].insert((*candidateIt));
                        }
                    }
                }
                expressionIt = _tempMonomes.erase(_tempMonomes.begin());
            }
            for( auto monomialIt = constraint->lhs().begin(); monomialIt != constraint->lhs().end(); ++monomialIt)
            {
                if( (*monomialIt)->monomial() == NULL || (*monomialIt)->monomial()->isAtMostLinear() )
                {
                    linearizedConstraint += **monomialIt;
                }
                else
                {
                    //cout << "Searching for: " << constraint->lhs() << " in Linearizations. Having: " << *(*monomialIt)->monomial() << endl;
                    assert(mLinearizations.find(Polynomial(*(*monomialIt)->monomial())) != mLinearizations.end());
                    linearizedConstraint += (*monomialIt)->coeff() * (*mLinearizations.find( Polynomial(*(*monomialIt)->monomial() ))).second;
                }
            }
        }
        assert(_tempMonomes.empty());
        return linearizedConstraint;
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
    
    
    void ICPModule::activateLinearEquations()
    {
        for( auto candidatesIt = mLinearConstraints.begin(); candidatesIt != mLinearConstraints.end(); ++candidatesIt )
        {
            ContractionCandidates candidates = (*candidatesIt).second;
            for( auto ccIt = candidates.begin(); ccIt != candidates.end(); ++ccIt )
            {
                if( (*ccIt)->constraint()->relation() == Relation::EQ )
                {
                    (*ccIt)->activate();
                }
            }
        }
    }
    

    void ICPModule::fillCandidates()
    {
        // fill mIcpRelevantCandidates with the nonlinear contractionCandidates
        for ( auto nonlinearIt = mActiveNonlinearConstraints.begin(); nonlinearIt != mActiveNonlinearConstraints.end(); ++nonlinearIt )
        {
            // check that assertions have been processed properly
            assert( (*nonlinearIt).second == (*nonlinearIt).first->origin().size() );
            assert( mIntervals.find((*nonlinearIt).first->derivationVar()) != mIntervals.end() );
#ifdef ICP_CONSIDER_WIDTH
            if ( mIntervals.at((*nonlinearIt).first->derivationVar()).diameter() > mTargetDiameter || mIntervals.at((*nonlinearIt).first->derivationVar()).diameter() == -1 )
#else
            if ( mIntervals.at((*nonlinearIt).first->derivationVar()).diameter() > 0 || mIntervals.at((*nonlinearIt).first->derivationVar()).diameter() == -1 )
#endif
            {
                // only add if not already existing
                if ( !findCandidateInRelevant((*nonlinearIt).first) )
                {
                    #ifdef ICPMODULE_DEBUG
                    cout << "add to relevant candidates: " << (*nonlinearIt).first->rhs() << endl;
                    cout << "   id: " << (*nonlinearIt).first->id() << endl;
                    #endif
                    addCandidateToRelevant((*nonlinearIt).first);
                }
            }
            else // the candidate is not relevant -> delete from icpRelevantCandidates
            {
                if ( findCandidateInRelevant((*nonlinearIt).first) )
                {
                    #ifdef ICPMODULE_DEBUG
                    cout << "remove from relevant candidates due to diameter: " << (*nonlinearIt).first->rhs() << endl;
                    cout << "   id: " << (*nonlinearIt).first->id() << " , Diameter: " << mIntervals[(*nonlinearIt).first->derivationVar()].diameter() << endl;
                    #endif
                    removeCandidateFromRelevant((*nonlinearIt).first);
                }
            }
        }

        // fill mIcpRelevantCandidates with the active linear contractionCandidates
        for ( auto linearIt = mActiveLinearConstraints.begin(); linearIt != mActiveLinearConstraints.end(); ++linearIt )
        {
            // check that assertions have been processed properly
            assert( (*linearIt).second == (*linearIt).first->origin().size() );
            assert( mIntervals.find((*linearIt).first->derivationVar()) != mIntervals.end() );
            
#ifdef ICP_CONSIDER_WIDTH
            if ( (*linearIt).first->isActive() && ( mIntervals.at((*linearIt).first->derivationVar()).diameter() > mTargetDiameter || mIntervals.at((*linearIt).first->derivationVar()).diameter() == -1 ) )
#else
            if ( (*linearIt).first->isActive() && ( mIntervals.at((*linearIt).first->derivationVar()).diameter() > 0 || mIntervals.at((*linearIt).first->derivationVar()).diameter() == -1 ) )
#endif
            {
                if( !findCandidateInRelevant((*linearIt).first) )
                {
                    #ifdef ICPMODULE_DEBUG
                    cout << "add to relevant candidates: " << (*linearIt).first->rhs() << endl;
                    cout << "   id: " << (*linearIt).first->id() << endl;
                    #endif
                    addCandidateToRelevant((*linearIt).first);
                }
            }
            else // the candidate is not relevant -> delete from icpRelevantCandidates
            {
                if ( findCandidateInRelevant((*linearIt).first) )
                {
                    #ifdef ICPMODULE_DEBUG
                    cout << "remove from relevant candidates due to diameter: " << (*linearIt).first->rhs() << endl;
                    cout << "   id: " << (*linearIt).first->id() << " , Diameter: " << mIntervals[(*linearIt).first->derivationVar()].diameter() << endl;
                    #endif
                    removeCandidateFromRelevant((*linearIt).first);
                }
            }
        }
    }
    
    
    bool ICPModule::addCandidateToRelevant(icp::ContractionCandidate* _candidate)
    {
        if ( _candidate->isActive() )
        {
            std::pair<double, unsigned> target(_candidate->RWA(), _candidate->id());
            if ( mIcpRelevantCandidates.find(target) == mIcpRelevantCandidates.end() )
            {
                mIcpRelevantCandidates.insert(target);
                return true;
            }
        }
        return false;
    }
    
    
    bool ICPModule::removeCandidateFromRelevant(icp::ContractionCandidate* _candidate)
    {
        for ( auto candidateIt = mIcpRelevantCandidates.begin(); candidateIt != mIcpRelevantCandidates.end(); ++candidateIt )
        {
            if ( _candidate->id() == (*candidateIt).second )
            {
                mIcpRelevantCandidates.erase(candidateIt);
                return true;
            }
        }
        return false;
    }
    
    
    bool ICPModule::findCandidateInRelevant(icp::ContractionCandidate* _candidate)
    {
        std::pair<double, unsigned> target(_candidate->RWA(), _candidate->id());
        return ( mIcpRelevantCandidates.find(target) != mIcpRelevantCandidates.end() );
    }
    
				
    void ICPModule::updateRelevantCandidates(carl::Variable _var, double _relativeContraction)
    {
        // update all candidates which contract in the dimension in which the split has happened
        std::set<icp::ContractionCandidate*> updatedCandidates;
        // iterate over all affected constraints
        std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(_var);
        assert(icpVar != mVariables.end());
        for ( auto candidatesIt = (*icpVar).second->candidates().begin(); candidatesIt != (*icpVar).second->candidates().end(); ++candidatesIt)
        {
            if ( (*candidatesIt)->isActive() )
            {
                unsigned id = (*candidatesIt)->id();
                // search if candidate is already contained - erase if, else do nothing
                if ( findCandidateInRelevant(*candidatesIt) )
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
                addCandidateToRelevant(*candidatesIt);
        }
    }
    
    
    icp::ContractionCandidate* ICPModule::chooseContractionCandidate()
    {
        assert(!mIcpRelevantCandidates.empty());
        // as the map is sorted ascending, we can simply pick the last value
        for ( auto candidateIt = mIcpRelevantCandidates.rbegin(); candidateIt != mIcpRelevantCandidates.rend(); ++candidateIt )
        {
            if ( mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->isActive() )//&& mIntervals[mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->derivationVar()].diameter() != 0 )
            {
                #ifdef ICPMODULE_DEBUG
                cout << "Chose Candidate: ";
                mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->print();
                cout << endl;
                #endif
                return mCandidateManager->getInstance()->getCandidate((*candidateIt).second);
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
        if(_selection->derivative() == 0)
            _selection->calcDerivative();

        const Polynomial               constr     = _selection->rhs();
        const Polynomial               derivative = _selection->derivative();
        const carl::Variable           variable   = _selection->derivationVar();
        assert(mIntervals.find(variable) != mIntervals.end());
        double                 originalDiameter = mIntervals.at(variable).diameter();
        bool originalUnbounded = ( mIntervals.at(variable).lowerBoundType() == carl::BoundType::INFTY || mIntervals.at(variable).upperBoundType() == carl::BoundType::INFTY );
        smtrat::DoubleInterval originalInterval = mIntervals.at(variable);
        
        splitOccurred    = _selection->contract( mIntervals, resultA, resultB );
        if( splitOccurred )
        {
            #ifdef ICPMODULE_DEBUG
            #ifndef ICPMODULE_REDUCED_DEBUG            
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
                    tmpRight.insert(std::pair<const carl::Variable,smtrat::DoubleInterval>(variable, resultA ));
                else
                    tmpRight.insert((*intervalIt));
            }

            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            std::vector<Formula*> partialBox = createConstraintsFromBounds(tmpRight);
            Formula* negBox = new Formula(NOT);
            Formula* boxConjunction = new Formula(AND);
            for ( auto formulaIt = partialBox.begin(); formulaIt != partialBox.end(); ++formulaIt )
                boxConjunction->addSubformula(*formulaIt);
            
            negBox->addSubformula(boxConjunction);
            mCheckContraction->addSubformula(negBox);
            partialBox.clear();
            #endif

            icp::HistoryNode* newRightChild = new icp::HistoryNode(tmpRight, mCurrentId+2);
            newRightChild->setSplit( icp::intervalToConstraint( variable,tmpRight.at(variable) ).first );
            mHistoryActual->addRight(newRightChild);
            #ifdef ICPMODULE_DEBUG
            #ifndef ICPMODULE_REDUCED_DEBUG
            cout << "Created node:" << endl;
            newRightChild->print();
            #endif
            #endif
            
            // left first!
            EvalDoubleIntervalMap tmpLeft = EvalDoubleIntervalMap();
            for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                    tmpLeft.insert(std::pair<const carl::Variable,smtrat::DoubleInterval>(variable, resultB ));
                else
                    tmpLeft.insert((*intervalIt));
            }
            #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
            partialBox = createConstraintsFromBounds(tmpLeft);
            Formula* negBox2 = new Formula(NOT);
            Formula* boxConjunction2 = new Formula(AND);
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
            #ifdef ICPMODULE_DEBUG
            #ifndef ICPMODULE_REDUCED_DEBUG            
            cout << "Created node:" << endl;
            newLeftChild->print();
            #endif
            #endif
            // update mIntervals - usually this happens when changing to a different box, but in this case it has to be done manually, otherwise mIntervals is not affected.
            mIntervals[variable] = resultB;
#else
            /// create prequesites: ((oldBox AND CCs) -> newBox) in CNF: (oldBox OR CCs) OR newBox 
            PointerSet<Formula> subformulas;
            PointerSet<Formula> splitPremise = createPremiseDeductions();
            for( const Formula* subformula : splitPremise )
                subformulas.insert( newNegation( subformula ) );
            // construct new box
            subformulas.insert( createBoxFormula() );
            // push deduction
            addDeduction( newFormula( OR, subformulas ) );

            // create split: (not h_b OR (Not x<b AND x>=b) OR (x<b AND Not x>=b) )
            assert(resultA.upperBoundType() != BoundType::INFTY );
            Rational bound = carl::rationalize<Rational>( resultA.upper() );
            Module::branchAt( Polynomial( variable ), bound, splitPremise, true );
#endif
            // TODO: Shouldn't it be the average of both contractions?
            _relativeContraction = (originalDiameter - resultB.diameter()) / originalInterval.diameter();
            _absoluteContraction = originalDiameter - resultB.diameter();
        }
        else
        {
            // set intervals
            mIntervals[variable] = resultA;
            #ifdef ICPMODULE_DEBUG
            cout << "      New interval: " << variable << " = " << mIntervals.at(variable) << endl;
            #endif
            if ( mIntervals.at(variable).upperBoundType() != carl::BoundType::INFTY && mIntervals.at(variable).lowerBoundType() != carl::BoundType::INFTY && !originalUnbounded )
            {
                if ( originalDiameter == 0 )
                {
                    _relativeContraction = 0;
                    _absoluteContraction = 0;
                }
                else
                {
                    _relativeContraction = 1 - (mIntervals.at(variable).diameter() / originalDiameter);
                    _absoluteContraction = originalDiameter - mIntervals.at(variable).diameter();
                }
            }
            else if ( originalUnbounded && mIntervals.at(variable).isUnbounded() == false ) // if we came from infinity and got a result, we achieve maximal relative contraction
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
            
            #ifdef ICPMODULE_DEBUG
            cout << "      Relative contraction: " << _relativeContraction << endl;
            #endif
        }
        return splitOccurred;
    }
    
    
    std::map<carl::Variable, double> ICPModule::createModel( bool antipoint ) const
    {
        // Note that we do not need to consider INFTY bounds in the calculation of the antipoint.
        std::map<carl::Variable, double> assignments;
        for( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
        {
            double value;
            switch( (*varIt).second->isInternalUpdated() )
            {
                case icp::Updated::BOTH:
                    if(antipoint)
                        value = mIntervals.at((*varIt).second->var()).lower();
                    else
                        value = mIntervals.at((*varIt).second->var()).sample();
                    break;
                case icp::Updated::LEFT:
                    if(antipoint)
                        value = mIntervals.at((*varIt).second->var()).lower();
                    else 
                    {
                        if (mIntervals.at((*varIt).second->var()).upperBoundType() == BoundType::INFTY)
                            value = std::ceil(mIntervals.at((*varIt).second->var()).lower());
                        else
                            value = mIntervals.at((*varIt).second->var()).upper();
                    }
                    break;
                case icp::Updated::RIGHT:
                    if(antipoint)
                        value = mIntervals.at((*varIt).second->var()).upper();
                    else
                    {
                        if (mIntervals.at((*varIt).second->var()).lowerBoundType() == BoundType::INFTY)
                            value = std::floor(mIntervals.at((*varIt).second->var()).upper());
                        else
                            value = mIntervals.at((*varIt).second->var()).lower();
                    }
                    break;
                case icp::Updated::NONE:
                    if(antipoint)
                        value = mIntervals.at((*varIt).second->var()).sample();
                    else
                    {
                        if (mIntervals.at((*varIt).second->var()).lowerBoundType() == BoundType::INFTY)
                            value = std::floor(mIntervals.at((*varIt).second->var()).upper());
                        else
                            value = mIntervals.at((*varIt).second->var()).lower();
                    }
                    break;
                default:
                    break;
            }
            assignments.insert( std::make_pair((*varIt).second->var(), value) );
        }
        return assignments;
    }
    
    
    void ICPModule::updateModel() const
    {
        clearModel();
        if( solverState() == True )
        {
            EvalRationalMap rationalAssignment;
            rationalAssignment = mLRA.getRationalModel();
            for( auto assignmentIt = rationalAssignment.begin(); assignmentIt != rationalAssignment.end(); ++assignmentIt )
            {
                auto varIt = mVariables.find((*assignmentIt).first);
                if(  varIt != mVariables.end() && (*varIt).second->isOriginal() )
                {
                    Polynomial value = Polynomial( assignmentIt->second );
                    Assignment assignment = vs::SqrtEx(value);
                    mModel.insert(mModel.end(), std::make_pair(assignmentIt->first, assignment));
                }
            }
        }
    }
    
    
    void ICPModule::tryContraction( icp::ContractionCandidate* _selection, double& _relativeContraction, EvalDoubleIntervalMap _intervals )
    {
        smtrat::DoubleInterval resultA = smtrat::DoubleInterval();
        smtrat::DoubleInterval resultB = smtrat::DoubleInterval();
        bool splitOccurred = false;

        // check if derivative is already calculated
        if(_selection->derivative() == 0)
            _selection->calcDerivative();

        const Polynomial               constr     = _selection->rhs();
        const Polynomial               derivative = _selection->derivative();
        const carl::Variable           variable   = _selection->derivationVar();
        assert(_intervals.find(variable) != _intervals.end());
        double                 originalDiameter = _intervals.at(variable).diameter();
        bool originalUnbounded = ( _intervals.at(variable).lowerBoundType() == carl::BoundType::INFTY || _intervals.at(variable).upperBoundType() == carl::BoundType::INFTY );
        
//        splitOccurred = mIcp.contract<GiNaCRA::SimpleNewton>( _intervals, constr, derivative, variable, resultA, resultB );
        splitOccurred    = _selection->contract( mIntervals, resultA, resultB );
        
        if( splitOccurred )
        {
            smtrat::DoubleInterval originalInterval = _intervals.at(variable);
            
            EvalDoubleIntervalMap tmpRight = EvalDoubleIntervalMap();
            for ( auto intervalIt = _intervals.begin(); intervalIt != _intervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                    tmpRight.insert(std::pair<const carl::Variable,smtrat::DoubleInterval>(variable, resultA ));
                else
                    tmpRight.insert((*intervalIt));
            }
            
            // left first!
            EvalDoubleIntervalMap tmpLeft = EvalDoubleIntervalMap();
            for ( auto intervalIt = _intervals.begin(); intervalIt != _intervals.end(); ++intervalIt )
            {
                if ( (*intervalIt).first == variable )
                    tmpLeft.insert(std::pair<const carl::Variable,smtrat::DoubleInterval>(variable, resultB ));
                else
                    tmpLeft.insert((*intervalIt));
            }
            _relativeContraction = (originalDiameter - resultB.diameter()) / originalInterval.diameter();
        }
        else
        {
            // set intervals
            _intervals[variable] = resultA;
            if ( _intervals.at(variable).upperBoundType() != carl::BoundType::INFTY && _intervals.at(variable).lowerBoundType() != carl::BoundType::INFTY && !originalUnbounded )
            {
                if ( originalDiameter == 0 )
                    _relativeContraction = 0;
                else
                    _relativeContraction = 1 - (_intervals.at(variable).diameter() / originalDiameter);
            }
            else if ( originalUnbounded && _intervals.at(variable).isUnbounded() == false ) // if we came from infinity and got a result, we achieve maximal relative contraction
                _relativeContraction = 1;
        }
    }
    
    
    double ICPModule::calculateSplittingImpact ( const carl::Variable& _var, icp::ContractionCandidate& _candidate ) const
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
        #ifdef ICPMODULE_DEBUG
        cout << __PRETTY_FUNCTION__ << " Rule " << mSplittingStrategy << ": " << impact << endl;
        #endif
        return impact;
    }
    

    PointerSet<Formula> ICPModule::createPremiseDeductions()
    {
        // collect applied contractions
        PointerSet<Formula> contractions = mHistoryActual->appliedConstraints();
        // collect original box
//        assert( mBoxStorage.size() == 1 );
        PointerSet<Formula> box = mBoxStorage.front();
        contractions.insert( box.begin(), box.end() );
        mBoxStorage.pop();
        return contractions;
    }
    
    
    const Formula* ICPModule::createBoxFormula()
    {
        Variables originalRealVariables;
        mpReceivedFormula->realValuedVars(originalRealVariables);
        PointerSet<Formula> subformulas;
        for( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
        {
            if( originalRealVariables.find( (*intervalIt).first ) != originalRealVariables.end() )
            {
                std::pair<const Constraint*, const Constraint*> boundaries = icp::intervalToConstraint((*intervalIt).first, (*intervalIt).second);
                if(boundaries.first != NULL)
                {
                    subformulas.insert( newFormula( boundaries.first ) );                       
                }
                if(boundaries.second != NULL)
                {
                    subformulas.insert( newFormula( boundaries.second ) );
                }
            }
        }
        return newFormula( AND, subformulas );
    }
    
    
    std::pair<bool,carl::Variable> ICPModule::checkAndPerformSplit( )
    {
        std::pair<bool,carl::Variable> result = std::make_pair(false, carl::Variable::NO_VARIABLE);
        bool found = false;
        carl::Variable variable = (*mIntervals.begin()).first; // Initialized to some dummy value
        double maximalImpact = 0;   
        // first check all intevals from nonlinear contractionCandidats -> backwards to begin at the most important candidate
        for ( auto candidateIt = mActiveNonlinearConstraints.rbegin(); candidateIt != mActiveNonlinearConstraints.rend(); ++candidateIt )
        {
            if(found)
                break;
            if ( (*candidateIt).first->isActive() )
            {
                variable = *(*candidateIt).first->constraint()->variables().begin();
                // search for the biggest interval and check if it is larger than the target Diameter
                for ( auto variableIt = (*candidateIt).first->constraint()->variables().begin(); variableIt != (*candidateIt).first->constraint()->variables().end(); ++variableIt )
                {
                    std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
                    assert(icpVar != mVariables.end());
                    if ( mIntervals.find(*variableIt) != mIntervals.end() && mIntervals.at(*variableIt).diameter() > mTargetDiameter && (*icpVar).second->isOriginal() )
                    {
                        if(mSplittingStrategy > 0)
                        {
                            double actualImpact = calculateSplittingImpact(*variableIt, *(*candidateIt).first);
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
        for ( auto candidateIt = mActiveLinearConstraints.rbegin(); candidateIt != mActiveLinearConstraints.rend(); ++candidateIt )
        {
            if(found)
                break;
            if ( (*candidateIt).first->isActive() )
            {
                variable = *(*candidateIt).first->constraint()->variables().begin();
                // search for the biggest interval and check if it is larger than the target Diameter
                for ( auto variableIt = (*candidateIt).first->constraint()->variables().begin(); variableIt != (*candidateIt).first->constraint()->variables().end(); ++variableIt )
                {
                    std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
                    assert(icpVar != mVariables.end());
                    if ( mIntervals.find(*variableIt) != mIntervals.end() && mIntervals.at(*variableIt).diameter() > mTargetDiameter && (*icpVar).second->isOriginal() )
                    {
                        if(mSplittingStrategy > 0)
                        {
                            double actualImpact = calculateSplittingImpact(*variableIt, *(*candidateIt).first);
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
        if ( found )
        {
            #ifndef BOXMANAGEMENT
            // create prequesites: ((oldBox AND CCs) -> newBox) in CNF: (oldBox OR CCs) OR newBox 
            PointerSet<Formula> splitPremise = createPremiseDeductions();
            PointerSet<Formula> subformulas;
            for( auto formulaIt = splitPremise.begin(); formulaIt != splitPremise.end(); ++formulaIt )
                subformulas.insert( newNegation( *formulaIt ) );
            // construct new box
            subformulas.insert( createBoxFormula() );
            // push deduction
            addDeduction( newFormula( OR, subformulas ) );
            
            // create split: (not h_b OR (Not x<b AND x>=b) OR (x<b AND Not x>=b) )
            Rational bound = carl::rationalize<Rational>( mIntervals.at(variable).sample() );
            Module::branchAt( Polynomial( variable ), bound, splitPremise, false );
            
            result.first = true;
            result.second = variable;
            return result;
            #else
            //perform split and add two historyNodes
            #ifdef ICPMODULE_DEBUG
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
            std::pair<const Constraint*, const Constraint*> boundaryConstraints = icp::intervalToConstraint(variable, tmpRightInt);
            newRightChild->setSplit(boundaryConstraints.first);
            mHistoryActual->addRight(newRightChild);

            // left first!
            DoubleInterval tmpLeftInt = tmp;
            tmpLeftInt.cutFrom(tmp.sample());
            tmpLeftInt.setRightType(BoundType::STRICT);
            mIntervals[variable] = tmpLeftInt;
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
            result.first = true;
            result.second = variable;
            std::map<string, icp::IcpVariable*>::iterator icpVar = mVariables.find(variable.get_name());
            assert(icpVar != mVariables.end());
            (*icpVar).second->setUpdated();
            return result;
            #endif
        }
        return result;
    }

    
    std::pair<bool,bool> ICPModule::validateSolution()
    {
        // call mLRA module
        vec_set_const_pFormula failedConstraints = vec_set_const_pFormula();
        PointerSet<Formula> currentInfSet;
        bool newConstraintAdded = false;
        bool boxCheck = false;
        #ifdef ICPMODULE_DEBUG
        cout << "[ICP] Call mLRAModule" << endl;
        #endif
#ifndef ICP_SIMPLE_VALIDATION
        // create new center constraints and add to validationFormula
        for ( auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt)
        {
            if ( (*variableIt).second->checkLinear() == false )
            {
                carl::Variable variable = (*variableIt).second->var();
                assert(mIntervals.find(variable) != mIntervals.end());
                smtrat::DoubleInterval interval = mIntervals.at(variable);

                smtrat::DoubleInterval center = smtrat::DoubleInterval(interval.sample());
                Polynomial constraint = Polynomial(variable) - Polynomial(carl::rationalize<Rational>(center.sample()));
                const Formula* centerTmpFormula = newFormula( newConstraint( constraint, Relation::EQ ) );
                mLRA.inform(centerTmpFormula->pConstraint());
                mCenterConstraints.insert(centerTmpFormula->pConstraint());
                mValidationFormula->push_back( centerTmpFormula );
            }
        }
        
        // assert all constraints in mValidationFormula
        // TODO: optimize! -> should be okay to just assert centerconstraints
        for ( auto valIt = mValidationFormula->begin(); valIt != mValidationFormula->end(); ++valIt)
            mLRA.assertSubformula(valIt);

        #ifdef ICPMODULE_DEBUG
        cout << "[mLRA] receivedFormula: " << endl;
        cout << mLRA.rReceivedFormula().toString() << endl;
        #endif
        mLRA.rReceivedFormula().updateProperties();
        Answer centerFeasible = mLRA.isConsistent();
        mLRA.clearDeductions();
        
        if ( centerFeasible == True )
        {
            // remove centerConstaints as soon as they are not longer needed.
            clearCenterConstraintsFromValidationFormula();
            // strong consistency check
            EvalRationalMap pointsolution = mLRA.getRationalModel();
            #ifdef ICPMODULE_DEBUG
            cout << "[mLRA] Pointsolution: " << pointsolution << endl;
            #endif
            /*
             * fill linear variables with pointsolution b, determine coefficients c
             * of nonlinear variables x, take lower or upper bound correspondingly.
             * For every active linear constraint:
             *          check:
             *          c*x <= e + d*b
             * e = constant part,
             * d = coefficient of linear variable
             */

            // For every active linear constraint:
            for ( auto linearIt = mActiveLinearConstraints.begin(); linearIt != mActiveLinearConstraints.end(); ++linearIt)
            {
                Polynomial constraint = (*linearIt).first->rhs();
                Polynomial nonlinearParts;
                Rational res = 0;
                bool isLeftInfty = false;
                bool isRightInfty = false;
                bool satisfied = false;
                
                constraint += (*linearIt).first->lhs();
                constraint = constraint.substitute(pointsolution);
                
                std::map<carl::Variable, Rational> nonlinearValues;
                
                for( auto term = constraint.begin(); term != constraint.end(); ++term)
                {
                    Variables vars;
                    if(!(*term)->monomial())
                    {
                        continue; // Todo: sure?
                    }
                    else
                    {
                        (*term)->monomial()->gatherVariables(vars);
                        if( (*term)->coeff() < 0 )
                        {
                            for(auto varIt = vars.begin(); varIt != vars.end(); ++varIt)
                            {
                                if(mIntervals.at(*varIt).lowerBoundType() != BoundType::INFTY)
                                    nonlinearValues.insert(std::make_pair(*varIt, carl::rationalize<Rational>(mIntervals.at(*varIt).lower())) );
                                else
                                    isLeftInfty = true;
                            }
                        }
                        else
                        {
                            for(auto varIt = vars.begin(); varIt != vars.end(); ++varIt)
                            {
                                if(mIntervals.at(*varIt).upperBoundType() != BoundType::INFTY) 
                                    nonlinearValues.insert(std::make_pair(*varIt, carl::rationalize<Rational>(mIntervals.at(*varIt).upper())) );
                                else
                                    isRightInfty = true;
                            }
                        }
                        if( !(isLeftInfty || isRightInfty) )
                        {  
                            carl::Term<Rational>* tmp = (*term)->monomial()->substitute(nonlinearValues, (*term)->coeff());
                            assert(tmp->isConstant());
                            nonlinearParts += tmp->coeff();
                        }
                        nonlinearValues.clear();
                    }
                }
                Rational val = 0;
                if(constraint.isConstant())
                {
                    constraint += nonlinearParts;
                    val = constraint.isZero() ? 0 : constraint.lcoeff();
                }
                
                switch ((*linearIt).first->constraint()->relation())
                {
                    case Relation::EQ: //CR_EQ = 0
                        satisfied = (val == 0 && !isLeftInfty && !isRightInfty);
                        break;
                    case Relation::NEQ: //CR_NEQ = 1
                        satisfied = (val != 0 || isLeftInfty || isRightInfty);
                        break;
                    case Relation::LESS: //CR_LESS = 2
                        satisfied = (val < 0 || isLeftInfty);
                        break;
                    case Relation::GREATER: //CR_GREATER = 3
                        satisfied = (val > 0 || isRightInfty);
                        break;
                    case Relation::LEQ: //CR_LEQ = 4
                        satisfied = (val <= 0 || isLeftInfty);
                        break;
                    case Relation::GEQ: //CR_GEQ = 5
                        satisfied = (val >= 0 || isRightInfty);
                        break;
                }
                #ifdef ICPMODULE_DEBUG
                #ifndef ICPMODULE_REDUCED_DEBUG
                cout << "[ICP] Validate: " << *linearIt->first->constraint() << " -> " << satisfied << " (" << constraint << ") " << endl;
                cout << "Candidate: ";
                linearIt->first->print();
                #endif
                #endif
                // Strong consistency check
                if ( !satisfied )
                {
                    // parse mValidationFormula to get pointer to formula to generate infeasible subset
                    for ( auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); ++formulaIt )
                    {
                        for( auto originIt = (*linearIt).first->rOrigin().begin(); originIt != (*linearIt).first->rOrigin().end(); ++originIt )
                        {
                            if ((*formulaIt)->pConstraint() == (*originIt)->pConstraint() )
                            {
                                currentInfSet.insert(*formulaIt);
                                break;
                            }
                        }
                    }
                }

            } // for every linear constraint
            
            if ( !currentInfSet.empty() )
                failedConstraints.insert(failedConstraints.end(), currentInfSet);
           
            ContractionCandidates candidates;
            if (!failedConstraints.empty() && !failedConstraints.begin()->empty())
            {
                // Todo: Das muss effizienter gehen! CORRECT?
                for ( auto vecIt = failedConstraints.begin(); vecIt != failedConstraints.end(); ++vecIt )
                {
                    for ( auto infSetIt = (*vecIt).begin(); infSetIt != (*vecIt).end(); ++infSetIt )
                    {
                        Polynomial newConstraint = (*infSetIt)->constraint().lhs();

                        // if the failed constraint is not a centerConstraint - Ignore centerConstraints
                        if ( mCenterConstraints.find((*infSetIt)->pConstraint()) == mCenterConstraints.end() )
                        {
                            auto iterB = mReplacements.find( *infSetIt );
                            // add candidates for all variables to icpRelevantConstraints                               
                            if ( iterB != mReplacements.end() )
                            {
                                // search for the candidates and add them as icpRelevant
                                for ( auto actCandidateIt = mActiveLinearConstraints.begin(); actCandidateIt != mActiveLinearConstraints.end(); ++actCandidateIt )
                                {

                                    if ( (*actCandidateIt).first->hasOrigin( iterB->second ) )
                                    {
                                        #ifdef ICPMODULE_DEBUG
                                        #ifndef ICPMODULE_REDUCED_DEBUG
                                        cout << "isActive ";
                                        (*actCandidateIt).first->print();
                                        cout <<  " : " << (*actCandidateIt).first->isActive() << endl;
                                        #endif
                                        #endif
                                        
                                        // if the candidate is not active we really added a constraint -> indicate the change
                                        if ( !(*actCandidateIt).first->isActive() )
                                        {
                                            (*actCandidateIt).first->activate();
                                            candidates.insert((*actCandidateIt).first);
                                            newConstraintAdded = true;
                                        }

                                        // activate all icpVariables for that candidate
                                        for ( auto variableIt = (*actCandidateIt).first->constraint()->variables().begin(); variableIt != (*actCandidateIt).first->constraint()->variables().end(); ++variableIt )
                                        {
                                            std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
                                            assert(icpVar != mVariables.end());
                                            (*icpVar).second->activate();
                                        }
                                    } // found correct linear replacement
                                } // iterate over active linear constraints
                            } // is a linearization replacement
                            else
                            {
                                //This should not happen
                                assert(false);
                            }
                        } // is no center constraint
                    }
                }
            }
            if(newConstraintAdded)
            {
                mHistoryActual->propagateStateInfeasibleConstraints();
                mHistoryActual->propagateStateInfeasibleVariables();
                icp::HistoryNode* found = tryToAddConstraint(candidates, mHistoryRoot->right());
                if(found == NULL)
                {
                    setBox(mHistoryRoot);
                    mHistoryActual = mHistoryActual->addRight(new icp::HistoryNode(mHistoryRoot->intervals(),2));
                    mCurrentId = mHistoryActual->id();
                }
                else
                    setBox(found);
            }
            return std::pair<bool,bool>(newConstraintAdded,true);
        }
        else if ( centerFeasible == False || centerFeasible == Unknown )
        {
            ContractionCandidates candidates;
            failedConstraints = mLRA.infeasibleSubsets();
            if (!failedConstraints.empty() && !failedConstraints.begin()->empty())
            {
                // Todo: Das muss effizienter gehen! CORRECT?
                for ( auto vecIt = failedConstraints.begin(); vecIt != failedConstraints.end(); ++vecIt )
                {
                    for ( auto infSetIt = (*vecIt).begin(); infSetIt != (*vecIt).end(); ++infSetIt )
                    {
                        // if the failed constraint is not a centerConstraint - Ignore centerConstraints
                        if ( mCenterConstraints.find((*infSetIt)->pConstraint()) == mCenterConstraints.end() )
                        {
                            // add candidates for all variables to icpRelevantConstraints  
                            auto iterB = mReplacements.find( *infSetIt );
                            if ( iterB != mReplacements.end() )
                            {
                                // search for the candidates and add them as icpRelevant
                                for ( auto actCandidateIt = mActiveLinearConstraints.begin(); actCandidateIt != mActiveLinearConstraints.end(); ++actCandidateIt )
                                {

                                    if ( (*actCandidateIt).first->hasOrigin( iterB->second ) )
                                    {
                                        #ifdef ICPMODULE_DEBUG
                                        #ifndef ICPMODULE_REDUCED_DEBUG                                        
                                        cout << "isActive ";
                                        (*actCandidateIt).first->print();
                                        cout <<  " : " << (*actCandidateIt).first->isActive() << endl;
                                        #endif
                                        #endif
                                        
                                        // if the candidate is not active we really added a constraint -> indicate the change
                                        if ( !(*actCandidateIt).first->isActive() )
                                        {
                                            (*actCandidateIt).first->activate();
                                            candidates.insert((*actCandidateIt).first);
                                            newConstraintAdded = true;
                                        }

                                        // activate all icpVariables for that candidate
                                        for ( auto variableIt = (*actCandidateIt).first->constraint()->variables().begin(); variableIt != (*actCandidateIt).first->constraint()->variables().end(); ++variableIt )
                                        {
                                            std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(*variableIt);
                                            assert(icpVar != mVariables.end());
                                            (*icpVar).second->activate();
                                        }
                                    } // found correct linear replacement
                                } // iterate over active linear constraints
                            } // is a linearization replacement
                            else
                            {
                                //This should not happen
                                assert(false);
                            }
                        } // is no center constraint
                    }
                }
            }
            clearCenterConstraintsFromValidationFormula();
            if(newConstraintAdded)
            {
                mHistoryActual->propagateStateInfeasibleConstraints();
                mHistoryActual->propagateStateInfeasibleVariables();
                icp::HistoryNode* found = tryToAddConstraint(candidates, mHistoryRoot->right());
                if(found == NULL)
                {
                    setBox(mHistoryRoot);
                    mHistoryActual = mHistoryActual->addRight(new icp::HistoryNode(mHistoryRoot->intervals(),2));
                    mCurrentId = 2;
                }
                else
                    setBox(found);
            }
        }
#else
        // set BoxCheck per default as true
        boxCheck = true;
        
        // validate the antipoint
        std::map<carl::Variable, double> antipoint = createModel(true);
        EvalDoubleIntervalMap tmp;
        for(auto value : antipoint)
        {
            tmp.insert(std::make_pair(value.first, DoubleInterval(value.second)));
        }
        ContractionCandidates candidates;
        for(auto candidate = mActiveLinearConstraints.begin(); candidate != mActiveLinearConstraints.end(); ++candidate)
        {
            const Constraint* constraint = (*candidate).first->constraint();
            unsigned isSatisfied = constraint->consistentWith(tmp);
            if(isSatisfied == 0)
            {
                if( !(*candidate).first->isActive() )
                {
                    candidates.insert((*candidate).first);
                    (*candidate).first->activate();
                    newConstraintAdded = true;
                }
                
            }
        }
        // if a change has happened we need to restart at the latest point possible
        if(newConstraintAdded)
        {
            mHistoryActual->propagateStateInfeasibleConstraints();
            mHistoryActual->propagateStateInfeasibleVariables();
            icp::HistoryNode* found = tryToAddConstraint(candidates, mHistoryRoot->right());
            if(found == NULL)
            {
                setBox(mHistoryRoot);
                mHistoryActual = mHistoryActual->addRight(new icp::HistoryNode(mHistoryRoot->intervals(),2));
                mCurrentId = mHistoryActual->id();
            }
            else
                setBox(found);
        }
        // autoactivate all icpVariables
        for(auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt)
        {
            (*varIt).second->autoActivate();
        }
#endif
        return std::pair<bool,bool>(newConstraintAdded,boxCheck);
    }

    
    void ICPModule::clearCenterConstraintsFromValidationFormula()
    {
        for ( auto centerIt = mValidationFormula->begin(); centerIt != mValidationFormula->end(); )
        {
            if ( mCenterConstraints.find((*centerIt)->pConstraint()) != mCenterConstraints.end() )
            {
                mLRA.removeSubformula(centerIt);
                centerIt = mValidationFormula->erase(centerIt);
            }
            else
                ++centerIt;
        }
        mCenterConstraints.clear();
    }
    

    bool ICPModule::checkBoxAgainstLinearFeasibleRegion()
    {
        std::vector<const Formula*> addedBoundaries = createConstraintsFromBounds(mIntervals);
        for( auto formulaIt = addedBoundaries.begin(); formulaIt != addedBoundaries.end(); ++formulaIt )
        {
            mLRA.inform((*formulaIt)->pConstraint());
            mValidationFormula->push_back( *formulaIt );
            mLRA.assertSubformula( --mValidationFormula->end() );
        }
        mLRA.rReceivedFormula().updateProperties();
        Answer boxCheck = mLRA.isConsistent();
        #ifdef ICPMODULE_DEBUG
        cout << "Boxcheck: " << boxCheck << endl;
        #endif
        #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
        if ( boxCheck == False )
        {
            Formula* actualAssumptions = new Formula(*mValidationFormula);
            Module::addAssumptionToCheck(*actualAssumptions,false,"ICP_BoxValidation");
        }
        #endif
        if( boxCheck != True )
        {
            vec_set_const_pFormula tmpSet = mLRA.infeasibleSubsets();
            for ( auto infSetIt = tmpSet.begin(); infSetIt != tmpSet.end(); ++infSetIt )
            {
                for ( auto formulaIt = (*infSetIt).begin(); formulaIt != (*infSetIt).end(); ++formulaIt )
                {
                    if( !(*formulaIt)->pConstraint()->isBound() )
                    {
//                        assert(mpReceivedFormula->contains(mReceivedFormulaMapping.at(*formulaIt)));
                        mHistoryActual->addInfeasibleConstraint((*formulaIt)->pConstraint());
                        for( auto variableIt = (*formulaIt)->constraint().variables().begin(); variableIt != (*formulaIt)->constraint().variables().end(); ++variableIt )
                        {
                            assert( mVariables.find(*variableIt) != mVariables.end() );
                            mHistoryActual->addInfeasibleVariable(mVariables.at(*variableIt));
                        }
                    }
                    else
                    {
                        assert( mVariables.find( *(*formulaIt)->pConstraint()->variables().begin() ) != mVariables.end() );
                        mHistoryActual->addInfeasibleVariable( mVariables.at( *(*formulaIt)->pConstraint()->variables().begin()) );
                    }
                }
            }
        }
        #ifdef ICP_PROLONG_CONTRACTION
        else
        {
            EvalIntervalMap bounds = mLRA.getVariableBounds();
            #ifdef ICPMODULE_DEBUG
            cout << "Newly obtained Intervals: " << endl;
            #endif
            for ( auto boundIt = bounds.begin(); boundIt != bounds.end(); ++boundIt )
            {
                if (mVariables.find((*boundIt).first) != mVariables.end())
                {
                    Interval tmp = (*boundIt).second;
                    //mHistoryRoot->addInterval((*boundIt).first, smtrat::DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType()) );
                    DoubleInterval newInterval = DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType() );
                    if( !(mIntervals.at((*boundIt).first) == newInterval) && mIntervals.at((*boundIt).first).contains(newInterval) )
                    {
                        #ifdef ICPMODULE_DEBUG
                        cout << (*boundIt).first << ": " << (*boundIt).second << endl;
                        #endif
                        double relativeContraction = (mIntervals.at((*boundIt).first).diameter() - newInterval.diameter()) / mIntervals.at((*boundIt).first).diameter();
                        mIntervals[(*boundIt).first] = newInterval;
                        mVariables.at((*boundIt).first)->setUpdated();
                        updateRelevantCandidates((*boundIt).first, relativeContraction);
                    }
                }
            }
            
            // get intervals for slackvariables
            const LRAModule::ExVariableMap slackVariables = mLRA.slackVariables();
            for ( auto slackIt = slackVariables.begin(); slackIt != slackVariables.end(); ++slackIt )
            {
                std::map<const LRAVariable*, ContractionCandidates>::iterator linIt = mLinearConstraints.find((*slackIt).second);
                if ( linIt != mLinearConstraints.end() )
                {
                    // dirty hack: expect lhs to be set and take first item of set of CCs --> Todo: Check if it is really set in the constructors of the CCs during inform and assert
                    Interval tmp = (*slackIt).second->getVariableBounds();
                    // keep root updated about the initial box.
                    //mHistoryRoot->rIntervals()[(*(*linIt).second.begin())->lhs()] = smtrat::DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType());
                    DoubleInterval newInterval = DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType() );
                    Variable var = (*(*linIt).second.begin())->lhs();
                    if( !(mIntervals.at(var) == newInterval) && mIntervals.at(var).contains(newInterval) )
                    {
                        double relativeContraction = (mIntervals.at(var).diameter() - newInterval.diameter()) / mIntervals.at(var).diameter();
                        mIntervals[var] = smtrat::DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType());
                        mVariables.at(var)->setUpdated();
                        updateRelevantCandidates(var, relativeContraction);
                        #ifdef ICPMODULE_DEBUG
                        #ifndef ICPMODULE_REDUCED_DEBUG
                        cout << "Added interval (slackvariables): " << var << " " << tmp << endl;
                        #endif
                        #endif
                    }
                }
            }
        }
        #endif
        
        
        // remove boundaries from mLRA module after boxChecking.
        for( auto boundIt = addedBoundaries.begin(); boundIt != addedBoundaries.end(); )
        {
            for (auto formulaIt = mValidationFormula->begin(); formulaIt != mValidationFormula->end(); )
            {
                if( (*boundIt)->constraint() == (*formulaIt)->constraint() )
                {
                    mLRA.removeSubformula(formulaIt);
                    formulaIt = mValidationFormula->erase(formulaIt);
                    break;
                }
                else
                {
                    ++formulaIt;
                }
            }
            boundIt = addedBoundaries.erase(boundIt);
        }
        
        mLRA.clearDeductions();
        assert(addedBoundaries.empty());
        
        if ( boxCheck == True )
            return true;
        return false;
    }
    
    
    icp::HistoryNode* ICPModule::chooseBox( icp::HistoryNode* _basis )
    {
        if ( _basis->isLeft() )
        {
            // if spliting constraint or the constraint resulting from a contraction
            // of the splitting constraint is included in the infeasible subset
            // skip the right box and continue.
            const carl::Variable variable = _basis->variable();
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
    

    void ICPModule::setBox( icp::HistoryNode* _selection )
    {
        assert(_selection != NULL);
        #ifdef ICPMODULE_DEBUG
        cout << "Set box -> " << _selection->id() << ", #intervals: " << mIntervals.size() << " -> " << _selection->intervals().size() << endl;
        #endif
        // set intervals - currently we don't change not contained intervals.
        for ( auto constraintIt = _selection->rIntervals().begin(); constraintIt != _selection->rIntervals().end(); ++constraintIt )
        {
            assert(mIntervals.find((*constraintIt).first) != mIntervals.end());
            // only update intervals which changed
            if ( !(mIntervals.at((*constraintIt).first)==(*constraintIt).second) )
            {
                mIntervals[(*constraintIt).first] = (*constraintIt).second;
                std::map<const carl::Variable, icp::IcpVariable*>::const_iterator icpVar = mVariables.find((*constraintIt).first);
//                cout << "Searching for " << (*intervalIt).first.get_name() << endl;
                assert(icpVar != mVariables.end());
                (*icpVar).second->setUpdated();
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
    
    
    icp::HistoryNode* ICPModule::saveSetNode(icp::HistoryNode* _old, const icp::HistoryNode* const _new)
    {
        if (_old != NULL)
        {
            if( *_old->parent() == *_new->parent() )
                return _old;
            else
                saveSetNode(_old->parent(), _new);
        }
        return mHistoryRoot;
    }
    
    
    icp::HistoryNode* ICPModule::tryToAddConstraint( ContractionCandidates _candidates, icp::HistoryNode* _node )
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


    bool ICPModule::pushBoundsToPassedFormula()
    {
        bool newAdded = false;
        Variables originalRealVariables;
        mpReceivedFormula->realValuedVars(originalRealVariables);

        for ( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
        {            
            const carl::Variable tmpSymbol = *variablesIt;
            std::map<const carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(tmpSymbol);
            assert(icpVar != mVariables.end());
            if ( icpVar != mVariables.end() )
            {
                if( (*icpVar).second->isExternalBoundsSet() == icp::Updated::BOTH || (*icpVar).second->isExternalUpdated() != icp::Updated::NONE )
                {
                    // generate both bounds, left first
                    if( (*icpVar).second->isExternalBoundsSet() == icp::Updated::NONE || 
                        (*icpVar).second->isExternalBoundsSet() == icp::Updated::RIGHT ||
                        (*icpVar).second->isExternalUpdated() == icp::Updated::LEFT ||
                        (*icpVar).second->isExternalUpdated() == icp::Updated::BOTH )
                    {
                        assert( mIntervals.find(tmpSymbol) != mIntervals.end() );
                        Rational bound = carl::rationalize<Rational>(mIntervals.at(tmpSymbol).lower() );
                        Polynomial leftEx = Polynomial(tmpSymbol) - Polynomial(bound);

                        const Constraint* leftTmp;
                        switch (mIntervals.at(tmpSymbol).lowerBoundType())
                        {
                            case carl::BoundType::STRICT:
                                leftTmp = newConstraint(leftEx, Relation::GREATER);
                                break;
                            case carl::BoundType::WEAK:
                                leftTmp = newConstraint(leftEx, Relation::GEQ);

                                break;
                            default:
                                leftTmp = NULL;
                        }
                        if ( leftTmp != NULL )
                        {
                            const Formula* leftBound = newFormula(leftTmp);
                            vec_set_const_pFormula origins;
                            PointerSet<Formula> emptyTmpSet;
                            origins.insert(origins.begin(), emptyTmpSet);

                            if ( (*icpVar).second->isExternalBoundsSet() == icp::Updated::LEFT )
                                removeSubformulaFromPassedFormula((*icpVar).second->externalLeftBound());
                            addConstraintToInform(leftTmp);
                            addSubformulaToPassedFormula( leftBound, move( origins ) );
                            (*icpVar).second->setExternalLeftBound(--mpPassedFormula->end());
                            newAdded = true;
                        }
                    }
                    
                    if( (*icpVar).second->isExternalBoundsSet() == icp::Updated::NONE || 
                        (*icpVar).second->isExternalBoundsSet() == icp::Updated::LEFT || 
                        (*icpVar).second->isExternalUpdated() == icp::Updated::RIGHT ||
                        (*icpVar).second->isExternalUpdated() == icp::Updated::BOTH )
                    {
                        // right:
                        Rational bound = carl::rationalize<Rational>(mIntervals.at(tmpSymbol).upper());
                        Polynomial rightEx = Polynomial(tmpSymbol) - Polynomial(bound);

                        const Constraint* rightTmp;
                        switch (mIntervals.at(tmpSymbol).upperBoundType())
                        {
                            case carl::BoundType::STRICT:
                                rightTmp = newConstraint(rightEx, Relation::LESS);

                                break;
                            case carl::BoundType::WEAK:
                                rightTmp = newConstraint(rightEx, Relation::LEQ);
                                break;
                            default:
                                rightTmp = NULL;
                        }
                        if ( rightTmp != NULL )
                        {

                            const Formula* rightBound = newFormula(rightTmp);
                            vec_set_const_pFormula origins;
                            PointerSet<Formula> emptyTmpSet;
                            origins.insert(origins.begin(), emptyTmpSet);

                            if ( (*icpVar).second->isExternalBoundsSet() == icp::Updated::RIGHT )
                                removeSubformulaFromPassedFormula((*icpVar).second->externalRightBound());

                            addConstraintToInform(rightTmp);
                            addSubformulaToPassedFormula( rightBound, move( origins ) );
                            (*icpVar).second->setExternalRightBound(--mpPassedFormula->end());
                            newAdded = true;
                        }
                    }
                }
            }
        }
        if (mIsBackendCalled)
            return newAdded;
        else
            return true;
    }
    
    
    PointerSet<Formula> ICPModule::variableReasonHull( icp::set_icpVariable& _reasons )
    {
        PointerSet<Formula> reasons;
        for( auto variableIt = _reasons.begin(); variableIt != _reasons.end(); ++variableIt )
        {
            if ((*variableIt)->lraVar() != NULL)
            {
                PointerSet<Formula> definingOrigins = (*variableIt)->lraVar()->getDefiningOrigins();
                for( auto formulaIt = definingOrigins.begin(); formulaIt != definingOrigins.end(); ++formulaIt )
                {
    //                cout << "Defining origin: " << **formulaIt << " FOR " << *(*variableIt) << endl;
                    bool hasAdditionalVariables = false;
                    Variables realValuedVars;
                    mpReceivedFormula->realValuedVars(realValuedVars);
                    for( auto varIt = realValuedVars.begin(); varIt != realValuedVars.end(); ++varIt )
                    {
                        if(*varIt != (*variableIt)->var() && (*formulaIt)->constraint().hasVariable(*varIt))
                        {
                            hasAdditionalVariables = true;
                            break;
                        }
                    }
                    if( hasAdditionalVariables)
                    {
    //                    cout << "Addidional variables." << endl;
                        for( auto receivedFormulaIt = mpReceivedFormula->begin(); receivedFormulaIt != mpReceivedFormula->end(); ++receivedFormulaIt )
                        {
                            if( (*receivedFormulaIt)->pConstraint()->hasVariable((*variableIt)->var()) && (*receivedFormulaIt)->pConstraint()->isBound() )
                            {
                                reasons.insert(*receivedFormulaIt);
    //                            cout << "Also add: " << **receivedFormulaIt << endl;
                            }
                        }
                    }
                    else
                    {
    //                    cout << "No additional variables." << endl;
                        for( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt )
                        {
                            if( *(*replacementIt).first == (**formulaIt) )
                            {
                                for( auto receivedFormulaIt = mpReceivedFormula->begin(); receivedFormulaIt != mpReceivedFormula->end(); ++receivedFormulaIt )
                                {
                                    if( (**receivedFormulaIt) == *(*replacementIt).second )
                                    {
                                        reasons.insert(*receivedFormulaIt);
                                        break;
                                    }
                                }
                                break;
                            }
                        }
                    } // has no additional variables
                }// for all definingOrigins
            }
        }
        return reasons;
    }
    
    
    PointerSet<Formula> ICPModule::constraintReasonHull( std::set<const Constraint*>& _reasons )
    {
        PointerSet<Formula> reasons;
        for ( auto constraintIt = _reasons.begin(); constraintIt != _reasons.end(); ++constraintIt )
        {
            for ( auto formulaIt = mpReceivedFormula->begin(); formulaIt != mpReceivedFormula->end(); ++formulaIt )
            {
                if ( *constraintIt == (*formulaIt)->pConstraint() )
                {
                    reasons.insert(*formulaIt);
                    break;
                }
            }
        }
        return reasons;
    }
    
    
    PointerSet<Formula> ICPModule::collectReasons( icp::HistoryNode* _node )
    {
        icp::set_icpVariable variables = _node->rStateInfeasibleVariables();
        for( auto varIt = variables.begin(); varIt != variables.end(); ++varIt )
        {
//            cout << "Collect Hull for " << (*varIt)->var().get_name() << endl;
            _node->variableHull((*varIt)->var(), variables);
        }
        PointerSet<Formula> reasons = variableReasonHull(variables);
        PointerSet<Formula> constraintReasons = constraintReasonHull(_node->rStateInfeasibleConstraints());
        reasons.insert(constraintReasons.begin(), constraintReasons.end());
        return reasons;
    }
    
    
    std::vector<const Formula*> ICPModule::createConstraintsFromBounds( const EvalDoubleIntervalMap& _map )
    {
        std::vector<const Formula*> addedBoundaries;
        Variables originalRealVariables;
        mpReceivedFormula->realValuedVars(originalRealVariables);
        for ( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
        {
            const carl::Variable tmpSymbol = *variablesIt;
            if ( _map.find(tmpSymbol) != _map.end() )
            {
                std::map<const carl::Variable, icp::IcpVariable*>::iterator pos = mVariables.find(tmpSymbol);
                if ( pos != mVariables.end() )
                {
                    if ( (*pos).second->isInternalBoundsSet() != icp::Updated::BOTH || (*pos).second->isInternalUpdated() != icp::Updated::NONE )
                    {
                        std::pair<const Constraint*, const Constraint*> boundaries = icp::intervalToConstraint(tmpSymbol, _map.at(tmpSymbol));
                        switch((*pos).second->isInternalBoundsSet())
                        {
                            case icp::Updated::LEFT:
                                if ( boundaries.second != NULL )
                                {
                                    const Formula* rightBound = newFormula(boundaries.second);
                                    (*pos).second->setInternalRightBound(rightBound);
                                    addedBoundaries.insert(addedBoundaries.end(), rightBound);
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Created upper boundary constraint: " << *rightBound << endl;
                                    #endif
                                    #endif
                                }
                                break;                                  
                            case icp::Updated::RIGHT:
                                if ( boundaries.first != NULL)
                                {
                                    const Formula* leftBound = newFormula(boundaries.first);
                                    (*pos).second->setInternalLeftBound(leftBound);
                                    addedBoundaries.insert(addedBoundaries.end(), leftBound);
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Created lower boundary constraint: " << *leftBound << endl;
                                    #endif
                                    #endif
                                }
                                break;
                            case icp::Updated::NONE:
                                if ( boundaries.first != NULL)
                                {
                                    const Formula* leftBound = newFormula(boundaries.first);
                                    (*pos).second->setInternalLeftBound(leftBound);
                                    addedBoundaries.insert(addedBoundaries.end(), leftBound);
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Created lower boundary constraint: " << *leftBound << endl;
                                    #endif
                                    #endif
                                }
                                if ( boundaries.second != NULL )
                                {
                                    const Formula* rightBound = newFormula(boundaries.second);
                                    (*pos).second->setInternalRightBound(rightBound);
                                    addedBoundaries.insert(addedBoundaries.end(), rightBound);
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Created upper boundary constraint: " << *rightBound << endl;
                                    #endif
                                    #endif
                                }
                            default: // Both have been set but some have been updated
                                break;
                        }
                        // check for updates
                        switch((*pos).second->isInternalUpdated())
                        {
                            case icp::Updated::LEFT:
                                if ( boundaries.first != NULL)
                                {
                                    const Formula* leftBound = newFormula(boundaries.first);
                                    (*pos).second->setInternalLeftBound(leftBound);
                                    addedBoundaries.insert(addedBoundaries.end(), leftBound);
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Created lower boundary constraint: " << *leftBound << endl;
                                    #endif
                                    #endif
                                }
                                break;                                  
                            case icp::Updated::RIGHT:
                                if ( boundaries.second != NULL )
                                {
                                    const Formula* rightBound = newFormula(boundaries.second);
                                    (*pos).second->setInternalRightBound(rightBound);
                                    addedBoundaries.insert(addedBoundaries.end(), rightBound);
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Created upper boundary constraint: " << *rightBound << endl;
                                    #endif
                                    #endif
                                }
                                break;
                            case icp::Updated::BOTH:
                                if ( boundaries.first != NULL)
                                {
                                    const Formula* leftBound = newFormula(boundaries.first);
                                    (*pos).second->setInternalLeftBound(leftBound);
                                    addedBoundaries.insert(addedBoundaries.end(), leftBound);
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Created lower boundary constraint: " << *leftBound << endl;
                                    #endif
                                    #endif
                                }
                                if ( boundaries.second != NULL )
                                {
                                    const Formula* rightBound = newFormula(boundaries.second);
                                    (*pos).second->setInternalRightBound(rightBound);
                                    addedBoundaries.insert(addedBoundaries.end(), rightBound);
                                    #ifdef ICPMODULE_DEBUG
                                    #ifndef ICPMODULE_REDUCED_DEBUG
                                    cout << "Created upper boundary constraint: " << *rightBound << endl;
                                    #endif
                                    #endif
                                }
                            default: // none has been updated
                                break;
                        }
                    }
                    else
                    {
                        addedBoundaries.insert(addedBoundaries.end(), (*pos).second->internalLeftBound());
                        addedBoundaries.insert(addedBoundaries.end(), (*pos).second->internalRightBound());
                    }
                }
            }
        }
        return addedBoundaries;
    }
    
    
    const Formula* ICPModule::transformDeductions( const Formula* _deduction )
    {
        if( _deduction->getType() == CONSTRAINT )
        {
            Polynomial lhs = _deduction->constraint().lhs();
            std::map<Variable, Polynomial> tmpSubstitutions;
            tmpSubstitutions.insert(mSubstitutions.begin(), mSubstitutions.end());
            lhs = lhs.substitute(tmpSubstitutions);
            const Constraint* constraint = newConstraint(lhs, _deduction->constraint().relation());
            // TODO
            const Formula* newRealDeduction = newFormula( constraint );
            mCreatedDeductions.insert(newRealDeduction);
            return newRealDeduction;
        }
        else if( _deduction->isBooleanCombination() )
        {
            mCreatedDeductions.insert(_deduction);
            return _deduction;
        }
        else
        {
            //should not happen
            assert(false);
            return NULL;
        }
    }
    
    
    void ICPModule::remapAndSetLraInfeasibleSubsets()
    {
        vec_set_const_pFormula tmpSet = mLRA.infeasibleSubsets();
        for ( auto infSetIt = tmpSet.begin(); infSetIt != tmpSet.end(); ++infSetIt )
        {
            PointerSet<Formula> newSet;
            for ( auto formulaIt = (*infSetIt).begin(); formulaIt != (*infSetIt).end(); ++formulaIt )
            {
                for ( auto replacementsIt = mReplacements.begin(); replacementsIt != mReplacements.end(); ++replacementsIt )
                {
                    if( (**formulaIt) == *(*replacementsIt).first )
                    {
                        for( auto receivedFormulaIt = mpReceivedFormula->begin(); receivedFormulaIt != mpReceivedFormula->end(); ++receivedFormulaIt )
                        {
                            if( *(*replacementsIt).second == (**receivedFormulaIt) )
                            {
                                newSet.insert(*receivedFormulaIt);
                                break;
                            }
                        }
                        break;
                    }
                }
                
//                assert(mReceivedFormulaMapping.find(*formulaIt) != mReceivedFormulaMapping.end());
//                newSet.insert(mReceivedFormulaMapping.at(*formulaIt));
//                assert(mpReceivedFormula->contains(mReceivedFormulaMapping.at(*formulaIt)));
            }
            assert(newSet.size() == (*infSetIt).size());
            mInfeasibleSubsets.push_back(newSet);
        }
    }
    
    
#ifdef ICP_BOXLOG
    void ICPModule::writeBox()
    {
        GiNaC::symtab originalRealVariables = mpReceivedFormula->realValuedVars();
        
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
                const Constraint* constraint = (*candidateIt)->constraint();
                cout << (*candidateIt)->id() << ": " << *constraint << endl;
            }
        }
        cout << "****************** active linear constraints ******************" << endl;
        for(auto activeLinearIt = mActiveLinearConstraints.begin(); activeLinearIt != mActiveLinearConstraints.end(); ++activeLinearIt){
            cout << "Count: " << (*activeLinearIt).second << " , ";
            (*activeLinearIt).first->print();
        }
        cout << "******************* active linear variables *******************" << endl;
        for (auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt )
        {
            if ( (*variableIt).second->checkLinear() )
                cout << (*variableIt).first << ", ";
        }
        cout << endl;
        cout << "******************** nonlinear constraints ********************" << endl;
        std::map<const Constraint*, ContractionCandidates>::iterator nonlinearIt;
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
        std::map<icp::ContractionCandidate*, unsigned>::iterator activeNonlinearIt;

        for(activeNonlinearIt = mActiveNonlinearConstraints.begin(); activeNonlinearIt != mActiveNonlinearConstraints.end(); ++activeNonlinearIt){
            cout << "Count: " << (*activeNonlinearIt).second << " , ";
            activeNonlinearIt->first->print();
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
        cout << "************************* Replacements ************************" << endl;
        for ( auto replacementIt = mReplacements.begin(); replacementIt != mReplacements.end(); ++replacementIt )
        {
            cout << *(*replacementIt).first << "  \t -> \t" << *(*replacementIt).second << endl;
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
            mCandidateManager->getInstance()->getCandidate((*candidateIt).second)->print();
        }
    }

    
    void ICPModule::printIntervals( bool _original )
    {
        for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
        {
            if( !_original || mVariables.at((*constraintIt).first)->isOriginal())
            {
                cout << (*constraintIt).first << " \t -> " << (*constraintIt).second << endl;
            }
        }
    }
} // namespace smtrat
