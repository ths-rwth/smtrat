/*
 * @file ICPModule.cpp
 * @author Stefan Schupp <stefan.schupp@rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * Created on October 16, 2012, 1:07 PM
 */

#include <map>
#include <iomanip>
#include "assert.h"
#include "../../solver/Manager.h"
#include "ICPModule.h"

//#define ICP_MODULE_DEBUG_0
//#define ICP_MODULE_DEBUG_1
//#define ICP_MODULE_DEBUG_2
//#define ICP_MODULE_SHOW_PROGRESS

#ifdef ICP_MODULE_DEBUG_2
#ifndef ICP_MODULE_DEBUG_1
#define ICP_MODULE_DEBUG_1
#endif
#endif

#ifdef ICP_MODULE_DEBUG_1
#ifndef ICP_MODULE_DEBUG_0
#define ICP_MODULE_DEBUG_0
#endif
#endif

namespace smtrat
{
    template<class Settings>
    ICPModule<Settings>::ICPModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings* , Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mCandidateManager(),
        mActiveNonlinearConstraints(),
        mActiveLinearConstraints(),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mNotEqualConstraints(),
        mVariables(),
        mIntervals(),
        mIcpRelevantCandidates(),
        mLinearizations(),
        mDeLinearizations(),
        mVariableLinearizations(),
        mSubstitutions(),
        mHistoryRoot(new icp::HistoryNode(mIntervals)),
        mHistoryActual(nullptr),
        mValidationFormula(new ModuleInput()),
        mLRAFoundAnswer( std::vector< std::atomic_bool* >( 1, new std::atomic_bool( false ) ) ),
        mLraRuntimeSettings(new RuntimeSettings),
        mLRA(MT_LRAModule, mValidationFormula, mLraRuntimeSettings, mLRAFoundAnswer),
        mLastCandidate(nullptr),
        mBoxStorage(),
        mIsIcpInitialized(false),
        mTargetDiameter(mpManager->logic() == Logic::QF_NIA ? Settings::target_diameter_nia : Settings::target_diameter_nra),
        mContractionThreshold(mpManager->logic() == Logic::QF_NIA ? Settings::contraction_threshold_nia : Settings::contraction_threshold_nra),
        mDefaultSplittingSize(mpManager->logic() == Logic::QF_NIA ? Settings::default_splitting_size_nia : Settings::default_splitting_size_nra),
        mSplittingHeuristic(mpManager->logic() == Logic::QF_NIA ? Settings::splitting_heuristic_nia : Settings::splitting_heuristic_nra),
        mNumberOfReusagesAfterTargetDiameterReached(Settings::number_of_reusages_after_target_diameter_reached),
        mRelativeContraction(0),
        mAbsoluteContraction(0),
        mCountBackendCalls(0),
        mGlobalBoxSize(0.0),
        mInitialBoxSize(0.0)
    {}

    template<class Settings>
    ICPModule<Settings>::~ICPModule()
    {
        while( !mLRAFoundAnswer.empty() )
        {
            std::atomic_bool* toDel = mLRAFoundAnswer.back();
            mLRAFoundAnswer.pop_back();
            delete toDel;
        }
        mLRAFoundAnswer.clear();
        delete mLraRuntimeSettings;
        delete mHistoryRoot;
        delete mValidationFormula;
        for( auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt )
            delete (*variableIt).second;
        mVariables.clear();
        #ifdef ICP_MODULE_SHOW_PROGRESS
        std::cout << std::endl;
        #endif
    }

    template<class Settings>
    bool ICPModule<Settings>::informCore( const FormulaT& _constraint )
    {
        #ifdef ICP_MODULE_DEBUG_1
        std::cout << "[ICP] inform: " << _constraint << std::endl;
        #endif  
        if( _constraint.getType() == carl::FormulaType::CONSTRAINT )
        {
            const ConstraintT& constraint = _constraint.constraint();
            if( !constraint.integerValued() )
                mDefaultSplittingSize = 1000;
            unsigned constraintConsistency = constraint.isConsistent();
            if( constraintConsistency == 2 && _constraint.constraint().relation() != carl::Relation::NEQ )
                addConstraint( _constraint );
            return constraintConsistency != 0;
        }
        return true;
    }

    template<class Settings>
    bool ICPModule<Settings>::addCore( ModuleInput::const_iterator _formula )
    {
        switch( _formula->formula().getType() )
        {
            case carl::FormulaType::FALSE:
            {
                FormulasT infSubSet;
                infSubSet.push_back( _formula->formula() );
                mInfeasibleSubsets.push_back( infSubSet );
                mFoundSolution.clear();
                return false;
            }
            case carl::FormulaType::TRUE:
            {
                return true;
            }
            case carl::FormulaType::CONSTRAINT:
            {
                const ConstraintT& constr = _formula->formula().constraint();
                // create and initialize slackvariables
                if( constr.satisfiedBy( mFoundSolution ) != 1 )
                    mFoundSolution.clear();
                if( !mIsIcpInitialized )
                {
                    // catch deductions
                    mLRA.init();
                    mLRA.updateDeductions();
                    for( const auto& ded : mLRA.deductions() )
                    {
                        #ifdef ICP_MODULE_DEBUG_2
                        std::cout << "Create deduction for: " << ded.first.toString(false,0,"",true,true,true ) << std::endl;
                        #endif
                        FormulaT deduction = getReceivedFormulas( ded.first );
                        addDeduction(deduction, ded.second);
                        #ifdef ICP_MODULE_DEBUG_2
                        std::cout << "Passed deduction: " << deduction.toString(false,0,"",true,true,true ) << std::endl;
                        #endif
                    }
                    mLRA.clearDeductions();
                    mIsIcpInitialized = true;
                }
                // Handle Not Equal separate
                if( constr.relation() == carl::Relation::NEQ ) {
                    mNotEqualConstraints.insert(_formula->formula());
                    addReceivedSubformulaToPassedFormula(_formula);
                    return true;
                }		
                #ifdef ICP_MODULE_DEBUG_1
                std::cout << "[ICP] Assertion: " << constr << std::endl;
                #endif
                if( !_formula->formula().constraint().isBound() )
                {
                    // TODO: here or somewhere later in isConsistent: remove constraints from passed formula which are implied by the current box
                    addSubformulaToPassedFormula( _formula->formula(), _formula->formula() );
                    for( auto& var : _formula->formula().constraint().variables() )
                        mVariables.at(var)->addOriginalConstraint( _formula->formula() );
                }
                // activate associated nonlinear contraction candidates
                if( !constr.lhs().isLinear() )
                    activateNonlinearConstraint( _formula->formula() );
                // lookup corresponding linearization - in case the constraint is already linear, mReplacements holds the constraint as the linearized one
                auto replacementIt = mLinearizations.find( _formula->formula() );
                assert( replacementIt != mLinearizations.end() );
                const FormulaT& replacementPtr = (*replacementIt).second;
                assert( replacementPtr.getType() == carl::FormulaType::CONSTRAINT );
                if( replacementPtr.constraint().isBound() )
                {
                    // considered constraint is activated but has no slack variable -> it is a boundary constraint
                    auto res = mValidationFormula->add( replacementPtr );
                    #ifdef ICP_MODULE_DEBUG_1
                    std::cout << "[mLRA] Assert bound constraint: " << replacementPtr << std::endl;
                    #endif
                    // If the constraint has not yet been part of the lramodule's received formula, assert it. If the
                    // lramodule already detects inconsistency, process its infeasible subsets.
                    if( res.second && !mLRA.add( res.first ) ) 
                    {
                        remapAndSetLraInfeasibleSubsets();
                        assert( !mInfeasibleSubsets.empty() );
                        return false;
                    }
                }
                else
                    activateLinearConstraint( replacementPtr, _formula->formula() );
                return true;
            }
            default:
            {
                return true;
            }
        }
        return true;
    }

    template<class Settings>
    void ICPModule<Settings>::removeCore( ModuleInput::const_iterator _formula )
    {
        if( _formula->formula().getType() != carl::FormulaType::CONSTRAINT )
            return;
        const ConstraintT& constr = _formula->formula().constraint();
        #ifdef ICP_MODULE_DEBUG_1
        std::cout << "[ICP] Remove Formula " << constr << std::endl;
        #endif
        assert( constr.isConsistent() == 2 );
        if( constr.relation() == carl::Relation::NEQ ) {
            mNotEqualConstraints.erase(_formula->formula());
            return;
        }
        if( !constr.isBound() )
        {
            for( auto& var : constr.variables() )
                mVariables.at(var)->addOriginalConstraint( _formula->formula() );
        }		
        // is it nonlinear?
        auto iter = mNonlinearConstraints.find( constr );
        if( iter != mNonlinearConstraints.end() )
        {
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "Nonlinear." << std::endl;
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
        assert( slackvariable != nullptr );
        // lookup if contraction candidates already exist - if so, add origins
        auto iterB = mLinearConstraints.find( slackvariable );
        if( iterB != mLinearConstraints.end() )
        {
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "Linear." << std::endl;
            #endif
            for( icp::ContractionCandidate* cc : iterB->second )
            {
                // remove candidate if counter == 1, else decrement counter.
                // TODO: as the origin has maybe already been removed with removing the origins of non-linear constraints
                // we need to check the following before. This should be avoided differently.
                if( cc->hasOrigin( _formula->formula() ) ) 
                {
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
        }
        // remove constraint from mLRA module
        auto replacementIt = mLinearizations.find( _formula->formula() );
        assert( replacementIt != mLinearizations.end() );
        auto validationFormulaIt = mValidationFormula->find( replacementIt->second );
        if( validationFormulaIt != mValidationFormula->end() )
        {
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "[mLRA] remove " << validationFormulaIt->formula().constraint() << std::endl;
            #endif
            mLRA.remove( validationFormulaIt );
            mValidationFormula->erase( validationFormulaIt );
        }
    }

    template<class Settings>
    Answer ICPModule<Settings>::checkCore( bool _full )
    {
        #ifdef ICP_MODULE_DEBUG_0
        std::cout << "##############################################################" << std::endl;
        std::cout << "Start consistency check with the ICPModule on the constraints " << std::endl;
        for( const auto& f : rReceivedFormula() )
            std::cout << "    " << f.formula().constraint() << std::endl;
        #endif
        if( !mFoundSolution.empty() )
        {
            #ifdef ICP_MODULE_DEBUG_0
            std::cout << "Found solution still feasible." << std::endl << std::endl;
            #endif
            if( checkNotEqualConstraints() )
                return True;
            else
                return Unknown;
        }
        for(;;)
        {
            // Debug Outputs of linear and nonlinear Tables
            #ifdef ICP_MODULE_DEBUG_0
            #ifdef ICP_MODULE_DEBUG_1
            printIcpVariables();
            #else
            std::cout << "Constraints after preprocessing:" << std::endl;
            printPreprocessedInput( "    " );
            std::cout << std::endl;
            #endif
            #endif
            for( icp::ContractionCandidate* cc : mActiveLinearConstraints )
                cc->resetReusagesAfterTargetDiameterReached();
            for( icp::ContractionCandidate* cc : mActiveNonlinearConstraints )
                cc->resetReusagesAfterTargetDiameterReached();
            Answer lraAnswer = Unknown;
            if( initialLinearCheck( lraAnswer ) )
            {
                if( lraAnswer == True ) {
                    carl::Variables originalRealVariables;
                    rReceivedFormula().realValuedVars(originalRealVariables); // TODO: store original variables as member, updating them efficiently with assert and remove
                    for( auto var : originalRealVariables )
                        mFoundSolution.emplace( var, ZERO_RATIONAL ); // Note, that it is only stored 0 as solution, if the variable has not yet a solution
                    if( checkNotEqualConstraints() )
                        return True;
                    else
                        return Unknown;
                }
                return lraAnswer;
            }
            #ifdef ICP_MODULE_SHOW_PROGRESS
            if( mGlobalBoxSize == 0.0 ) mGlobalBoxSize = calculateCurrentBoxSize();
            mInitialBoxSize = calculateCurrentBoxSize();
            #endif
            #ifdef ICP_MODULE_DEBUG_0
            std::cout << "Start with the intervals" << std::endl;
            printIntervals( false );
            #endif
            bool invalidBox = contractCurrentBox();
            #ifdef ICP_MODULE_DEBUG_0
            std::cout << std::endl;
            #endif
            // when one interval is empty, we can skip validation and chose next box.
            if( invalidBox ) // box contains no solution
            {
                #ifdef ICP_MODULE_DEBUG_0
                std::cout << "Whole box contains no solution! Return False." << std::endl;
                #endif
                // whole box forms infeasible subset
                mInfeasibleSubsets.push_back( createPremiseDeductions() );
                #ifdef ICP_MODULE_SHOW_PROGRESS
                addProgress( mInitialBoxSize );
                #endif
                return False;
            }
            else
            {
                assert( !intervalsEmpty() );
                if( mSplitOccurred )
                {
                    #ifdef ICP_MODULE_DEBUG_0
                    std::cout << "Return unknown, raise deductions for split." << std::endl;
                    #endif
                    assert( !splittings().empty() );
                    return Unknown;
                }
                assert( splittings().empty() );
                if( tryTestPoints() )
                {
                    if( checkNotEqualConstraints() )
                        return True;
                    else
                        return Unknown;
                }
                else
                {
                    // create Bounds and set them, add to passedFormula
                    pushBoundsToPassedFormula();
                    // lazy call of the backends on found box
                    Answer lazyResult = callBackends( false );
                    // if it led to a result or the backends require a splitting
                    if( lazyResult != Unknown || !splittings().empty() )
                        return lazyResult;
                    // Full call of the backends, if no box has target diameter
                    bool furtherContractionOccurred = false;
                    if( !performSplit( mOriginalVariableIntervalContracted, furtherContractionOccurred ) )
                        return callBackends( _full );
                    if( furtherContractionOccurred )
                        continue;
                    assert( splittings().size() == 1 );
                    return Unknown; // Splitting required
                }
            }
        }
    }
    
    template<class Settings>
    void ICPModule<Settings>::resetHistory( icp::ContractionCandidate* _cc )
    {
        if( mHistoryActual == nullptr )
            return;
        if(mHistoryActual->getCandidates().find(_cc) != mHistoryActual->getCandidates().end())
        {
            setBox(mHistoryRoot);
            mHistoryActual->reset();
        }
    }
    
    template<class Settings>
    void ICPModule<Settings>::addConstraint( const FormulaT& _formula )
    {
        assert( _formula.getType() == carl::FormulaType::CONSTRAINT );
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
                    mSubstitutions.insert( std::make_pair( *var, carl::makePolynomial<Poly>(*var) ) );
                    getIcpVariable( *var, true, nullptr ); // note that we have to set the lra variable later
                    mHistoryRoot->addInterval( *var, DoubleInterval::unboundedInterval() );
                }
            }
            // actual preprocessing
            FormulaT linearFormula = FormulaT( carl::FormulaType::TRUE );
            if( constr.isLinear() )
                linearFormula = _formula;
            else
            {
                assert( mLinearizations.find( _formula ) == mLinearizations.end() );
                std::vector<Poly> temporaryMonomes = icp::getNonlinearMonomials( constr );
                assert( !temporaryMonomes.empty() );
                Poly lhs = createNonlinearCCs( _formula.constraint(), temporaryMonomes );
                linearFormula = FormulaT( lhs, constraint.relation() );
                assert( linearFormula.constraint().lhs().isLinear() );
                #ifdef ICP_MODULE_DEBUG_1
                std::cout << "linearize constraint to   " << linearFormula.constraint() << std::endl;
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
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "[mLRA] inform: " << linearizedConstraint << std::endl;
            #endif
            if( !linearizedConstraint.isBound() )
                createLinearCCs( linearFormula );
            // set the lra variables for the icp variables regarding variables (introduced and original ones)
            // TODO: Refactor this last part - it seems to be too complicated
            for( auto var = linearizedConstraint.variables().begin(); var != linearizedConstraint.variables().end(); ++var )
            {
                auto iter = mVariables.find( *var );
                assert( iter != mVariables.end() );
                if( iter->second->lraVar() == nullptr )
                {
                    auto ovarIter = mLRA.originalVariables().find( *var );
                    if( ovarIter != mLRA.originalVariables().end() )
                        iter->second->setLraVar( ovarIter->second );
                }
            }
        }
    }
    
    template<class Settings>
    icp::IcpVariable* ICPModule<Settings>::getIcpVariable( carl::Variable::Arg _var, bool _original, const LRAVariable* _lraVar )
    {
        auto iter = mVariables.find( _var );
        if( iter != mVariables.end() )
            return iter->second;
        auto res = mIntervals.insert( std::make_pair( _var, DoubleInterval::unboundedInterval() ) );
        assert( res.second );
        icp::IcpVariable* icpVar = new icp::IcpVariable( _var, _original, passedFormulaEnd(), res.first, _lraVar );
        mVariables.insert( std::make_pair( _var, icpVar ) );
        return icpVar;
    }
    
    template<class Settings>
    void ICPModule<Settings>::activateNonlinearConstraint( const FormulaT& _formula )
    {
        assert( _formula.getType() == carl::FormulaType::CONSTRAINT );
        auto iter = mNonlinearConstraints.find( _formula.constraint() );
        #ifdef ICP_MODULE_DEBUG_1
        std::cout << "[ICP] Assertion (nonlinear)" << _formula.constraint() <<  std::endl;
        std::cout << "mNonlinearConstraints.size: " << mNonlinearConstraints.size() << std::endl;
        std::cout << "Number Candidates: " << iter->second.size() << std::endl;
        #endif
        for( auto candidateIt = iter->second.begin(); candidateIt != iter->second.end(); ++candidateIt )
        {
            if( (*candidateIt)->activity() == 0 )
            {
                mActiveNonlinearConstraints.insert( *candidateIt );
                #ifdef ICP_MODULE_DEBUG_1
                std::cout << "[ICP] Activated candidate: ";
                (*candidateIt)->print();
                #endif
            }
            (*candidateIt)->addOrigin( _formula );
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "[ICP] Increased candidate count: ";
            (*candidateIt)->print();
            #endif
        }
    }
    
    template<class Settings>
    void ICPModule<Settings>::activateLinearConstraint( const FormulaT& _formula, const FormulaT& _origin )
    {
        assert( _formula.getType() == carl::FormulaType::CONSTRAINT );
        const LRAVariable* slackvariable = mLRA.getSlackVariable( _formula );
        assert( slackvariable != nullptr );
        // lookup if contraction candidates already exist - if so, add origins
        auto iter = mLinearConstraints.find( slackvariable );
        assert( iter != mLinearConstraints.end() );
        for ( auto candidateIt = iter->second.begin(); candidateIt != iter->second.end(); ++candidateIt )
        {
            #ifdef ICP_MODULE_DEBUG_2
            std::cout << "[ICP] ContractionCandidates already exist: ";
            slackvariable->print();
            std::cout << ", Size Origins: " << (*candidateIt)->origin().size() << std::endl;
            std::cout << _formula << std::endl;
            (*candidateIt)->print();
            std::cout << "Adding origin." << std::endl;
            #endif
            // set value in activeLinearConstraints
            if( (*candidateIt)->activity() == 0 )
                mActiveLinearConstraints.insert( *candidateIt );
            // add origin
            (*candidateIt)->addOrigin( _origin );
        }

        // assert in mLRA
        auto res = mValidationFormula->add( _formula );
        if( res.second )
        {
            if( !mLRA.add( res.first ) )
                remapAndSetLraInfeasibleSubsets();
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "[mLRA] Assert " << _formula << std::endl;
            #endif
        }
    }
    
    template<class Settings>
    bool ICPModule<Settings>::checkNotEqualConstraints() 
    {
        for( auto& constraint : mNotEqualConstraints ) 
        {
            if( constraint.satisfiedBy(mFoundSolution) == 0 ) 
            {
                splitUnequalConstraint(constraint);
                #ifdef ICP_MODULE_DEBUG_0
                std::cout << "Unresolved inequality " << constraint << "  -  Return unknown and raise deductions for split." << std::endl;
                #endif
                return false;
            }
        }
        return true;
    }
    
    template<class Settings>
    bool ICPModule<Settings>::contractCurrentBox()
    {
        #ifdef ICP_MODULE_DEBUG_0
        std::cout << __func__ << ":" << std::endl;
        #endif
        bool invalidBox = false;
        mLastCandidate = nullptr;
        mSplitOccurred = false;
        mOriginalVariableIntervalContracted = false;
        for( ; ; )
        {
            while(!mBoxStorage.empty())
                mBoxStorage.pop();
            icp::set_icpVariable icpVariables;
            carl::Variables originalRealVariables;
            rReceivedFormula().realValuedVars(originalRealVariables); // TODO: store original variables as member, updating them efficiently with assert and remove
            for( auto variablesIt = originalRealVariables.begin(); variablesIt != originalRealVariables.end(); ++variablesIt )
            {
                auto iter = mVariables.find(*variablesIt);
                if( iter != mVariables.end() )
                    icpVariables.insert( iter->second );
            }
            FormulaSetT box = variableReasonHull(icpVariables);
            mBoxStorage.push(box);
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "********************** [ICP] Contraction **********************" << std::endl;
            //cout << "Subtree size: " << mHistoryRoot->sizeSubtree() << std::endl;
            mHistoryActual->print();
            #endif
            // prepare IcpRelevantCandidates
            fillCandidates();
            while ( !mIcpRelevantCandidates.empty() && !mSplitOccurred )
            {
                icp::ContractionCandidate* candidate = chooseContractionCandidate();
                assert(candidate != nullptr);
                mRelativeContraction = -1; // TODO: try without this line
                mAbsoluteContraction = 0; // TODO: try without this line
                contraction( candidate );
                // catch if new interval is empty -> we can drop box and chose next box
                if ( mIntervals.at(candidate->derivationVar()).isEmpty() )
                {
                    #ifdef ICP_MODULE_DEBUG_0
                    std::cout << "Contracted to empty interval!" << std::endl;
                    #endif
                    mLastCandidate = candidate;
                    invalidBox = true;
                    break;
                }
                if( (mRelativeContraction > 0 || mAbsoluteContraction > 0) && originalRealVariables.find( candidate->derivationVar() ) != originalRealVariables.end() )
                {
                    mLastCandidate = candidate;
                    mOriginalVariableIntervalContracted = true;
                }
                // update weight of the candidate
                removeCandidateFromRelevant(candidate);
                candidate->setPayoff(mRelativeContraction);
                candidate->calcRWA();
                // only add nonlinear CCs as linear CCs should only be used once
                if( !candidate->isLinear() )
                    addCandidateToRelevant(candidate); // TODO: Improve - no need to add irrelevant candidates (see below)
                assert(mIntervals.find(candidate->derivationVar()) != mIntervals.end() );
                if ( (mRelativeContraction < mContractionThreshold && !mSplitOccurred) || fulfillsTarget(*candidate) )
                    removeCandidateFromRelevant(candidate);
                else if ( mRelativeContraction >= mContractionThreshold )
                {
                    // make sure all candidates which contain the variable of which the interval has significantly changed are contained in mIcpRelevantCandidates.
                    std::map<carl::Variable, icp::IcpVariable*>::iterator icpVar = mVariables.find(candidate->derivationVar());
                    assert(icpVar != mVariables.end());
                    for ( auto candidateIt = (*icpVar).second->candidates().begin(); candidateIt != (*icpVar).second->candidates().end(); ++candidateIt )
                    {
                        bool toAdd = true;
                        // TODO: there must be a better way to find out whether the candidate is already in the relevants
                        for ( auto relevantCandidateIt = mIcpRelevantCandidates.begin(); relevantCandidateIt != mIcpRelevantCandidates.end(); ++relevantCandidateIt )
                        {
                            if ( (*relevantCandidateIt).second == (*candidateIt)->id() )
                                toAdd = false;
                        }
                        if ( toAdd && (*candidateIt)->isActive() && !fulfillsTarget(**candidateIt) )
                            addCandidateToRelevant(*candidateIt);
                    }
                }
            } //while ( !mIcpRelevantCandidates.empty() && !mSplitOccurred)
            // verify if the box is already invalid
            if( !invalidBox && !mSplitOccurred )
            {
                invalidBox = !checkBoxAgainstLinearFeasibleRegion();
                #ifdef ICP_MODULE_DEBUG_1
                std::cout << "Invalid against linear region: " << (invalidBox ? "yes!" : "no!") << std::endl;
                #endif
            }
            if( invalidBox )
                return true;
            if( mSplitOccurred || mIcpRelevantCandidates.empty() ) // relevantCandidates is not empty, if we got new bounds from LRA during boxCheck
                return false;
        }
        assert( false ); // should not happen
        return invalidBox;
    }
    
    template<class Settings>
    Answer ICPModule<Settings>::callBackends( bool _full )
    {
        #ifdef ICP_MODULE_DEBUG_0
        std::cout << "Ask backends " << (_full ? "full" : "lazy") << " for the satisfiability of:" << std::endl;
        for( const auto& f : rPassedFormula() )
            std::cout << "    " << f.formula().constraint() << std::endl;
        #endif
        ++mCountBackendCalls;
        Answer a = runBackends( _full );
        updateDeductions();
        if( !Settings::use_backends_splitting_decisions )
            clearSplittings();
        std::vector<Module*>::const_iterator backend = usedBackends().begin();
        while( backend != usedBackends().end() )
        {
            (*backend)->clearDeductions();
            ++backend;
        }
        #ifdef ICP_MODULE_DEBUG_0
        std::cout << "  Backend's answer: " << ANSWER_TO_STRING( a ) << std::endl;
        #endif
        if( a == False )
        {
            assert(infeasibleSubsets().empty());
            FormulasT contractionConstraints = this->createPremiseDeductions();
            backend = usedBackends().begin();
            while( backend != usedBackends().end() )
            {
                assert( !(*backend)->infeasibleSubsets().empty() );
                #ifdef ICP_MODULE_DEBUG_1
                (*backend)->printInfeasibleSubsets();
                #endif
                for( auto infsubset = (*backend)->infeasibleSubsets().begin(); infsubset != (*backend)->infeasibleSubsets().end(); ++infsubset )
                {
                    FormulasT newInfSubset;
                    for( auto subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                    {
                        if( !subformula->constraint().isBound() )
                            newInfSubset.push_back( *subformula );
                    }
                    newInfSubset.insert( newInfSubset.end(), contractionConstraints.begin(), contractionConstraints.end() );
                    mInfeasibleSubsets.push_back( newInfSubset );
                }
                ++backend;
            }
            #ifdef ICP_MODULE_SHOW_PROGRESS
            addProgress( mInitialBoxSize );
            #endif
            return False;
        }
        else // if answer == true or answer == unknown
        {
            mHistoryActual->propagateStateInfeasibleConstraints(mHistoryRoot);
            mHistoryActual->propagateStateInfeasibleVariables(mHistoryRoot);
            return a;
        }
    }
        
    template<class Settings>
    Poly ICPModule<Settings>::createNonlinearCCs( const ConstraintT& _constraint, const std::vector<Poly>& _tempMonomes )
    {
        Poly linearizedConstraint = ZERO_POLYNOMIAL;
        ContractionCandidates ccs;
        /*
         * Create all icp variables and contraction candidates for the given non-linear constraint:
         * 
         *      a_1*m_1 + .. + a_k*m_k ~ b, with b and a_i being rationals and m_i being monomials (possibly linear)
         */
        for( auto& monom : _tempMonomes )
        {
            ContractionCandidates ccsOfMonomial;
            auto iter = mVariableLinearizations.find( monom );
            if( iter == mVariableLinearizations.end() ) // no linearization yet
            {
                // create mLinearzations entry
                carl::Variables variables;
                monom.gatherVariables( variables );
                bool hasRealVar = false;
                for( auto var = variables.begin(); var != variables.end(); ++var )
                {
                    if( var->getType() == carl::VariableType::VT_REAL )
                    {
                        hasRealVar = true;
                        break;
                    }
                }
                carl::Variable newVar = hasRealVar ? carl::freshRealVariable() : carl::freshIntegerVariable();
                mVariableLinearizations.insert( std::make_pair( monom, newVar ) );
                mSubstitutions.insert( std::make_pair( newVar, monom ) );
                assert( mVariables.find( newVar ) == mVariables.end() );
                icp::IcpVariable* icpVar = getIcpVariable( newVar, false, nullptr );
                mHistoryRoot->addInterval( newVar, DoubleInterval::unboundedInterval() );
                #ifdef ICP_MODULE_DEBUG_1
                std::cout << "New replacement: " << monom << " -> " << mVariableLinearizations.at(monom) << std::endl;
                #endif
                // Create equation m_i - v_i = 0, where m_i is the nonlinear monomial x_{i,1}^e_{i,1}*..*x_{i,n}^e_{i,n} being replaced by the freshly introduced variable v_i
                const Poly rhs = monom - carl::makePolynomial<Poly>(newVar);
                if( mContractors.find(rhs) == mContractors.end() )
                    mContractors.insert(std::make_pair(rhs, Contractor<carl::SimpleNewton>(rhs)));
                
                ConstraintT tmp = ConstraintT( rhs, carl::Relation::EQ );
                for( auto varIndex = variables.begin(); varIndex != variables.end(); ++varIndex )
                {
                    // create a contraction candidate for m_i-v_i regarding the variable x_{i,1}
                    icp::ContractionCandidate* tmpCandidate = mCandidateManager.createCandidate( newVar, rhs, tmp, *varIndex, mContractors.at( rhs ) );
                    ccsOfMonomial.insert( ccsOfMonomial.end(), tmpCandidate );
                    tmpCandidate->setNonlinear();
                    // add the contraction candidate to the icp variable of v_i
                    auto tmpIcpVar = mVariables.find( newVar );
                    assert( tmpIcpVar != mVariables.end() );
                    tmpIcpVar->second->addCandidate( tmpCandidate );
                }
                // create a contraction candidate for m_i-v_i regarding the variable v_i
                icp::ContractionCandidate* tmpCandidate = mCandidateManager.createCandidate( newVar, rhs, tmp, newVar, mContractors.at( rhs ) );
                tmpCandidate->setNonlinear();
                icpVar->addCandidate( tmpCandidate );
                ccsOfMonomial.insert( ccsOfMonomial.end(), tmpCandidate );
                // add all contraction candidates for m_i-v_i to the icp variables of all x_{i,j}
                for( auto var = variables.begin(); var != variables.end(); ++var )
                {
                    auto origIcpVar = mVariables.find( *var );
                    assert( origIcpVar != mVariables.end() );
                    origIcpVar->second->addCandidates( ccsOfMonomial );
                }
                ccs.insert( ccsOfMonomial.begin(), ccsOfMonomial.end() );
            }
            else // already existing replacement/substitution/linearization
            {
                #ifdef ICP_MODULE_DEBUG_2
                std::cout << "Existing replacement: " << monom << " -> " << mVariableLinearizations.at(monom) << std::endl;
                #endif
                auto iterB = mVariables.find( iter->second );
                assert( iterB != mVariables.end() );
                // insert already created CCs into the current list of CCs
                ccs.insert( iterB->second->candidates().begin(), iterB->second->candidates().end() );
            }
        }
        // Construct the linearization
        for( auto monomialIt = _constraint.lhs().polynomial().begin(); monomialIt != _constraint.lhs().polynomial().end(); ++monomialIt )
        {
            if( (monomialIt)->monomial() == nullptr || (monomialIt)->monomial()->isAtMostLinear() )
                linearizedConstraint += carl::makePolynomial<Poly>(typename Poly::PolyType(*monomialIt));
            else
            {
                assert( mVariableLinearizations.find(carl::makePolynomial<Poly>(typename Poly::PolyType((monomialIt)->monomial()))) != mVariableLinearizations.end() );
                linearizedConstraint += (monomialIt)->coeff() * carl::makePolynomial<Poly>((*mVariableLinearizations.find( carl::makePolynomial<Poly>(typename Poly::PolyType((monomialIt)->monomial())) )).second);
            }
        }
        mNonlinearConstraints.emplace( _constraint, std::move(ccs) );
        linearizedConstraint *= _constraint.lhs().coefficient();
        return linearizedConstraint;
    }
    
    template<class Settings>
    void ICPModule<Settings>::createLinearCCs( const FormulaT& _constraint)
    {
        /*
         * Create all icp variables and contraction candidates for the given linear constraint:
         * 
         *      a_1*x_1 + .. + a_k*x_k ~ b, with b and a_i being rationals and x_i being variables
         */
        assert( _constraint.getType() == carl::FormulaType::CONSTRAINT );
        assert( _constraint.constraint().lhs().isLinear() );
        const LRAVariable* slackvariable = mLRA.getSlackVariable( _constraint );
        assert( slackvariable != nullptr );
        if( mLinearConstraints.find( slackvariable ) == mLinearConstraints.end() )
        {
            carl::Variables variables = _constraint.constraint().variables();
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
            variables.insert( variables.end(), newVar );
            mSubstitutions.insert( std::make_pair( newVar, carl::makePolynomial<Poly>( newVar ) ) );
            assert( mVariables.find( newVar ) == mVariables.end() );
            icp::IcpVariable* icpVar = getIcpVariable( newVar, false, slackvariable );
            mHistoryRoot->addInterval( newVar, DoubleInterval::unboundedInterval() );
            // Create equation a_1'*x_1 + .. + a_k'*x_k = 0, with a_i' = a_i/gcd(a_1,..,a_k)*sgn(a_1)
            const Poly rhs = carl::makePolynomial<Poly>(slackvariable->expression()) - carl::makePolynomial<Poly>(newVar);
            ConstraintT tmpConstr = ConstraintT( rhs, carl::Relation::EQ );
            auto iter = mContractors.find( rhs );
            if( iter == mContractors.end() )
                iter = mContractors.insert( std::make_pair( rhs, Contractor<carl::SimpleNewton>(rhs) ) ).first;
            ContractionCandidates ccs;
            // Create candidates for every possible variable:
            for( auto var = variables.begin(); var != variables.end(); ++var )
            {
                // create a contraction candidate for a_1'*x_1 + .. + a_k'*x_k - v regarding the variable x_i/v
                icp::ContractionCandidate* newCandidate = mCandidateManager.createCandidate( newVar, rhs, tmpConstr, *var, iter->second );
                ccs.insert( ccs.end(), newCandidate );
                newCandidate->setLinear();
            }
            // add all contraction candidates for a_1'*x_1 + .. + a_k'*x_k - v to the icp variables of all x_i/v
            for( auto var = variables.begin(); var != variables.end(); ++var )
            {
                auto origIcpVar = mVariables.find( *var );
                assert( origIcpVar != mVariables.end() );
                origIcpVar->second->addCandidates( ccs );
            }
            mLinearConstraints.insert( pair<const LRAVariable*, ContractionCandidates>( slackvariable, icpVar->candidates() ) );
        }
    }
    
    template<class Settings>
    void ICPModule<Settings>::fillCandidates()
    {
        // fill mIcpRelevantCandidates with the nonlinear contractionCandidates
        for ( icp::ContractionCandidate* nonlinearIt : mActiveNonlinearConstraints )
        {
            // check that assertions have been processed properly
            assert( (*nonlinearIt).activity() == (*nonlinearIt).origin().size() );
            if ( !fulfillsTarget(*nonlinearIt) )
                addCandidateToRelevant( nonlinearIt );// only add if not already existing
            else // the candidate is not relevant -> delete from icpRelevantCandidates
                removeCandidateFromRelevant(nonlinearIt);
        }
        // fill mIcpRelevantCandidates with the active linear contractionCandidates
        for ( icp::ContractionCandidate* linearIt : mActiveLinearConstraints )
        {
            // check that assertions have been processed properly
            assert( (*linearIt).activity() == (*linearIt).origin().size() );
            if ( (*linearIt).isActive() && !fulfillsTarget(*linearIt) )
                addCandidateToRelevant( linearIt );
            else // the candidate is not relevant -> delete from icpRelevantCandidates
                removeCandidateFromRelevant( linearIt );
        }
    }
    
    template<class Settings>
    bool ICPModule<Settings>::addCandidateToRelevant(icp::ContractionCandidate* _candidate)
    {
        if ( _candidate->isActive() )
        {
            mIcpRelevantCandidates.erase( std::pair<double, unsigned>( _candidate->lastRWA(), _candidate->id() ) );
            std::pair<double, unsigned> target(_candidate->RWA(), _candidate->id());
            if ( mIcpRelevantCandidates.find(target) == mIcpRelevantCandidates.end() )
            {
                #ifdef ICP_MODULE_DEBUG_1
                std::cout << "add to relevant candidates: " << (*_candidate).rhs() << " in variable " << (*_candidate).derivationVar() << std::endl;
                std::cout << "   id: " << (*_candidate).id() << std::endl;
                std::cout << "   key: (" << target.first << ", " << target.second << ")" << std::endl;
                #endif
                mIcpRelevantCandidates.insert(target);
                _candidate->updateLastRWA();
                return true;
            }
        }
        return false;
    }
    
    template<class Settings>
    bool ICPModule<Settings>::removeCandidateFromRelevant(icp::ContractionCandidate* _candidate)
    {
        std::pair<double, unsigned> target(_candidate->lastRWA(), _candidate->id());
        auto iter = mIcpRelevantCandidates.find( target );
        if( iter != mIcpRelevantCandidates.end() )
        {
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "remove from relevant candidates: " << (*_candidate).rhs() << std::endl;
            std::cout << "   id: " << (*_candidate).id() << " , Diameter: " << mIntervals[(*_candidate).derivationVar()].diameter() << std::endl;
            #endif
            mIcpRelevantCandidates.erase(iter);
            return true;
        }
        return false;
    }
    				
    template<class Settings>
    void ICPModule<Settings>::updateRelevantCandidates(carl::Variable::Arg _var)
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
                mCandidateManager.getCandidate(id)->setPayoff(mRelativeContraction );
                mCandidateManager.getCandidate(id)->calcRWA();
                updatedCandidates.insert(*candidatesIt);
            }
        }
        // re-insert tuples into icpRelevantCandidates
        for ( auto candidatesIt = updatedCandidates.begin(); candidatesIt != updatedCandidates.end(); ++candidatesIt )
        {
            if ( !fulfillsTarget(**candidatesIt) )
                addCandidateToRelevant(*candidatesIt);
        }
    }
    
    template<class Settings>
    icp::ContractionCandidate* ICPModule<Settings>::chooseContractionCandidate()
    {
        assert(!mIcpRelevantCandidates.empty());
        // as the map is sorted ascending, we can simply pick the last value
        for( auto candidateIt = mIcpRelevantCandidates.rbegin(); candidateIt != mIcpRelevantCandidates.rend(); ++candidateIt )
        {
            icp::ContractionCandidate* cc = mCandidateManager.getCandidate((*candidateIt).second);
            assert( cc != nullptr );
            if( cc->isActive() )//&& mIntervals[mCandidateManager.getCandidate((*candidateIt).second)->derivationVar()].diameter() != 0 )
            {
                cc->calcDerivative();
                #ifdef ICP_MODULE_DEBUG_1
                std::cout << "Choose Candidate: ";
                cc->print();
                std::cout << std::endl;
                #endif
                return cc;
            }
        }
        return nullptr;
    }
    
    template<class Settings>
    void ICPModule<Settings>::contraction( icp::ContractionCandidate* _selection )
    {
        DoubleInterval resultA;
        DoubleInterval resultB;
        // check if derivative is already calculated
        if(_selection->derivative().isZero())
            _selection->calcDerivative();
        carl::Variable variable = _selection->derivationVar();
        assert( mVariables.find( variable ) != mVariables.end() );
        icp::IcpVariable& icpVar = *mVariables.find( variable )->second;
        const DoubleInterval icpVarIntervalBefore = icpVar.interval();
        mSplitOccurred = _selection->contract( mIntervals, resultA, resultB );
        if( mSplitOccurred )
        {
            assert( !resultB.isEmpty() );
            #ifdef ICP_MODULE_DEBUG_2   
            std::cout << "Split occurred: " << resultA << " and " << resultB << std::endl;
            #endif
            icp::set_icpVariable variables;
            for( auto variableIt = _selection->constraint().variables().begin(); variableIt != _selection->constraint().variables().end(); ++variableIt )
            {
                assert(mVariables.find(*variableIt) != mVariables.end());
                variables.insert(mVariables.at(*variableIt));
            }
            mHistoryActual->addContraction(_selection, variables);
            /// create prequesites: ((oldBox AND CCs) -> newBox) in CNF: (oldBox OR CCs) OR newBox 
            FormulaSetT subformulas;
            std::vector<FormulaT> splitPremise = createPremise();
            for( const FormulaT& subformula : splitPremise )
                subformulas.insert( FormulaT( carl::FormulaType::NOT, subformula ) );
            // construct new box
            FormulaSetT boxFormulas = createBoxFormula();
            // push deduction
            if( boxFormulas.size() > 1 )
            {
                auto lastFormula = --boxFormulas.end();
                for( auto iter = boxFormulas.begin(); iter != lastFormula; ++iter )
                {
                    FormulaSetT subFormulaSetTmp = subformulas;
                    subFormulaSetTmp.insert( *iter );
                    addDeduction( FormulaT( carl::FormulaType::OR, subFormulaSetTmp ) );
                }
            }
            #ifdef ICP_MODULE_SHOW_PROGRESS
            addProgress( mInitialBoxSize - calculateCurrentBoxSize() );
            #endif
            // create split: (not h_b OR (Not x<b AND x>=b) OR (x<b AND Not x>=b) )
            assert(resultA.upperBoundType() != carl::BoundType::INFTY );
            Rational bound = carl::rationalize<Rational>( resultA.upper() );
            Module::branchAt( variable, bound, std::move(splitPremise), true, true );
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "division causes split on " << variable << " at " << bound << "!" << std::endl << std::endl;
            #endif
            updateRelativeContraction( icpVarIntervalBefore, resultA );
            updateAbsoluteContraction( icpVarIntervalBefore, resultA );
            #ifdef ICP_MODULE_DEBUG_0
            printContraction( *_selection, icpVarIntervalBefore, resultA, resultB );
            #endif
        }
        else
        {
            // set intervals
            setContraction( _selection, icpVar, icpVarIntervalBefore, resultA );
        }
        #ifdef ICP_MODULE_DEBUG_1
        std::cout << "      Relative contraction: " << mRelativeContraction << std::endl;
        #endif
    }
    
    template<class Settings>
    void ICPModule<Settings>::setContraction( icp::ContractionCandidate* _selection, icp::IcpVariable& _icpVar, const DoubleInterval& _interval, const DoubleInterval& _contractedInterval )
    {
        _icpVar.setInterval( _contractedInterval );
        #ifdef ICP_MODULE_DEBUG_1
        std::cout << "      New interval: " << variable << " = " << mIntervals.at(variable) << std::endl;
        #endif
        updateRelativeContraction( _interval, _contractedInterval );
        updateAbsoluteContraction( _interval, _contractedInterval );
        #ifdef ICP_MODULE_DEBUG_0
        printContraction( *_selection, _interval, _contractedInterval );
        #endif
        if (mRelativeContraction > 0 || mAbsoluteContraction > 0)
        {
            mHistoryActual->addInterval(_selection->lhs(), mIntervals.at(_selection->lhs()));
            icp::set_icpVariable variables;
            for( auto variableIt = _selection->constraint().variables().begin(); variableIt != _selection->constraint().variables().end(); ++variableIt )
            {
                assert(mVariables.find(*variableIt) != mVariables.end());
                variables.insert(mVariables.at(*variableIt));
            }
            mHistoryActual->addContraction(_selection, variables);
        }
    }
    
    template<class Settings>
    icp::ContractionCandidate* ICPModule<Settings>::getContractionCandidate( const FormulaT& _constraint, carl::Variable::Arg _var ) const
    {
        if( _constraint.constraint().lhs().isLinear() )
        {
            auto iter = mLinearConstraints.find( mLRA.getSlackVariable( _constraint ) );
            assert( iter != mLinearConstraints.end() );
            for( const auto& cc : iter->second )
            {
                if( cc->lhs() == _var )
                    return cc;
            }
        }
        else
        {
            assert( _constraint.getType() == carl::FormulaType::CONSTRAINT );
            auto iter = mNonlinearConstraints.find( _constraint.constraint() );
            assert( iter != mNonlinearConstraints.end() );
            for( const auto& cc : iter->second )
            {
                if( cc->lhs() == _var )
                    return cc;
            }
        }
        return nullptr;
    }
    
    template<class Settings>
    void ICPModule<Settings>::updateRelativeContraction( const DoubleInterval& _interval, const DoubleInterval& _contractedInterval )
    {
        assert( _interval == _contractedInterval || _interval.contains( _contractedInterval ) );
        if( _contractedInterval.isEmpty() )
        {
            mRelativeContraction = 1;
            return;
        }
        if( _interval == _contractedInterval )
        {
            mRelativeContraction = 0;
            return;
        }
        if( (_interval.lowerBoundType() == carl::BoundType::INFTY && _contractedInterval.lowerBoundType() != carl::BoundType::INFTY)
            || (_interval.upperBoundType() == carl::BoundType::INFTY && _contractedInterval.upperBoundType() != carl::BoundType::INFTY) )
        {
            mRelativeContraction = 1;
            return;
        }
        if( _contractedInterval.lowerBoundType() == carl::BoundType::INFTY || _contractedInterval.upperBoundType() == carl::BoundType::INFTY )
        {
            mRelativeContraction = 0;
            return;
        }
        assert( _interval.lowerBoundType() != carl::BoundType::INFTY );
        assert( _interval.upperBoundType() != carl::BoundType::INFTY );
        assert( _contractedInterval.lowerBoundType() != carl::BoundType::INFTY );
        assert( _contractedInterval.upperBoundType() != carl::BoundType::INFTY );
        mRelativeContraction = (double)1 - (_contractedInterval.diameter()/_interval.diameter());
    }
    
    template<class Settings>
    void ICPModule<Settings>::updateAbsoluteContraction( const DoubleInterval& _interval, const DoubleInterval& _contractedInterval )
    {
        assert( _interval == _contractedInterval || _interval.contains( _contractedInterval ) );
        if( _contractedInterval.isEmpty() )
        {
            if( _interval.lowerBoundType() == carl::BoundType::INFTY || _interval.upperBoundType() == carl::BoundType::INFTY )
                mAbsoluteContraction = std::numeric_limits<double>::infinity();
            else
                mAbsoluteContraction = _interval.diameter();
            return;
        }
        if( _interval == _contractedInterval )
        {
            mAbsoluteContraction = 0;
            return;
        }
        if( (_interval.lowerBoundType() == carl::BoundType::INFTY && _contractedInterval.lowerBoundType() != carl::BoundType::INFTY)
            || (_interval.upperBoundType() == carl::BoundType::INFTY && _contractedInterval.upperBoundType() != carl::BoundType::INFTY) )
        {
            mAbsoluteContraction = std::numeric_limits<double>::infinity();
            return;
        }
        if( _contractedInterval.lowerBoundType() == carl::BoundType::INFTY )
        {
            assert( _interval.upperBoundType() != carl::BoundType::INFTY );
            assert( _contractedInterval.lowerBoundType() == carl::BoundType::INFTY );
            assert( _contractedInterval.upperBoundType() != carl::BoundType::INFTY );
            assert( _interval.upper() >= _contractedInterval.upper() ); // >= as _contractedInterval.upperBoundType() could be strict and _interval.upperBoundType() weak
            mAbsoluteContraction = _interval.upper() - _contractedInterval.upper();
            if( _interval.upperBoundType() == carl::BoundType::WEAK && _contractedInterval.upperBoundType() == carl::BoundType::STRICT )
                mAbsoluteContraction = std::nextafter( mAbsoluteContraction, INFINITY );
            else if( _interval.upperBoundType() == carl::BoundType::STRICT && _contractedInterval.upperBoundType() == carl::BoundType::WEAK )
                mAbsoluteContraction = std::nextafter( mAbsoluteContraction, -INFINITY );
            return;
        }
        if( _contractedInterval.upperBoundType() == carl::BoundType::INFTY )
        {
            assert( _interval.lowerBoundType() != carl::BoundType::INFTY );
            assert( _contractedInterval.upperBoundType() == carl::BoundType::INFTY );
            assert( _contractedInterval.lowerBoundType() != carl::BoundType::INFTY );
            assert( _interval.lower() <= _contractedInterval.lower() ); // >= as _contractedInterval.lowerBoundType() could be strict and _interval.lowerBoundType() weak
            mAbsoluteContraction = _contractedInterval.lower() - _interval.lower();
            if( _interval.lowerBoundType() == carl::BoundType::WEAK && _contractedInterval.lowerBoundType() == carl::BoundType::STRICT )
                mAbsoluteContraction = std::nextafter( mAbsoluteContraction, INFINITY );
            else if( _interval.lowerBoundType() == carl::BoundType::STRICT && _contractedInterval.lowerBoundType() == carl::BoundType::WEAK )
                mAbsoluteContraction = std::nextafter( mAbsoluteContraction, -INFINITY );
            return;
        }
        assert( _interval.lowerBoundType() != carl::BoundType::INFTY );
        assert( _interval.upperBoundType() != carl::BoundType::INFTY );
        assert( _contractedInterval.lowerBoundType() != carl::BoundType::INFTY );
        assert( _contractedInterval.upperBoundType() != carl::BoundType::INFTY );
        mAbsoluteContraction = _interval.diameter() - _contractedInterval.diameter();
    }
    
    template<class Settings>
    std::map<carl::Variable, double> ICPModule<Settings>::createModel( bool antipoint ) const
    {
        // Note that we do not need to consider INFTY bounds in the calculation of the antipoint.
        std::map<carl::Variable, double> assignments;
        auto varIntervalIt = mIntervals.begin();
        for( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
        {
            assert( varIntervalIt->first == varIt->first );
            assert( varIt->second->var() == varIt->first );
            double value = 0;
            const DoubleInterval& interv = varIntervalIt->second; 
            if( !interv.isInfinite() )
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
                    if(interv.isPointInterval())
                        value = interv.lower();
                    else
                        value = interv.sample(false);
                }
                else if( takeLower )
                {
                    if( interv.lowerBoundType() == carl::BoundType::INFTY )
                    {
                        if( interv.upperBoundType() == carl::BoundType::WEAK )
                            value = interv.upper();
                        else
                            value = std::nextafter( interv.upper(), -INFINITY );
                    }
                    else
                    {
                        if( interv.lowerBoundType() == carl::BoundType::WEAK )
                            value = interv.lower();
                        else
                        {
                            value = std::nextafter( interv.lower(), INFINITY );
                            // Check if the interval does contain any double. If not, return an empty model.
                            if( value > interv.upper() || (interv.upperBoundType() == carl::BoundType::STRICT && value == interv.upper()) )
                                return std::map<carl::Variable, double>();
                        }
                    }
                }
                else
                {
                    if( interv.upperBoundType() == carl::BoundType::INFTY )
                    {
                        if( interv.lowerBoundType() == carl::BoundType::WEAK )
                            value = interv.lower();
                        else
                            value = std::nextafter( interv.lower(), INFINITY );
                    }
                    else
                    {
                        if( interv.upperBoundType() == carl::BoundType::WEAK )
                            value = interv.upper();
                        else
                        {
                            value = std::nextafter( interv.upper(), -INFINITY );
                            // Check if the interval does contain any double. If not, return an empty model.
                            if( value < interv.lower() || (interv.lowerBoundType() == carl::BoundType::STRICT && value == interv.lower()) )
                                return std::map<carl::Variable, double>();
                        }
                    }
                }
            }
            assert( interv.contains( value ) );
            assignments.insert( std::make_pair(varIt->first, value) );
            ++varIntervalIt;
        }
        return assignments;
    }
    
    template<class Settings>
    void ICPModule<Settings>::updateModel() const
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
                    if( varIt != mVariables.end() && (*varIt).second->isOriginal() )
                    {
                        Poly value = Poly( assignmentIt->second );
                        ModelValue assignment = vs::SqrtEx(value);
                        mModel.insert( std::make_pair( assignmentIt->first, assignment ) );
                    }
                }
            }
        }
    }
    
    template<class Settings>
    ModuleInput::iterator ICPModule<Settings>::eraseSubformulaFromPassedFormula( ModuleInput::iterator _subformula, bool _ignoreOrigins )
    {
        // TODO: check if the sub-formula is a bound, then take the variable, find its icp-variable and update it
        for( auto& varIcpvarPair : mVariables )
        {
            icp::IcpVariable& icpVar = *varIcpvarPair.second;
            assert( icpVar.externalLeftBound() == passedFormulaEnd() || icpVar.externalLeftBound() != icpVar.externalRightBound() );
            if( icpVar.externalLeftBound() == _subformula )
            {
                icpVar.setExternalLeftBound( passedFormulaEnd() );
                icpVar.setExternalModified();
                break;
            }
            else if( icpVar.externalRightBound() == _subformula )
            {
                icpVar.setExternalRightBound( passedFormulaEnd() );
                icpVar.setExternalModified();
                break;
            }
        }
        auto res = Module::eraseSubformulaFromPassedFormula( _subformula, _ignoreOrigins );
        return res;
    }
    
    template<class Settings>
    double ICPModule<Settings>::sizeBasedSplittingImpact( std::map<carl::Variable, icp::IcpVariable*>::const_iterator _varIcpVarMapIter ) const
    {
        const DoubleInterval& varInterval = _varIcpVarMapIter->second->interval();
        if( varInterval.lowerBoundType() == carl::BoundType::INFTY || varInterval.upperBoundType() == carl::BoundType::INFTY )
            return std::numeric_limits<double>::infinity();
        double impact = 0;
        double originalDiameter = varInterval.diameter();
        switch(mSplittingStrategy)
        {
            case 1: // Select biggest interval
            {
                impact = originalDiameter;
                break;
            }
            case 2: // Rule of Hansen and Walster - select interval with most varying function values
            {
                EvalDoubleIntervalMap tmpIntervals = mIntervals;
                tmpIntervals.insert(std::make_pair(_varIcpVarMapIter->first,DoubleInterval(1)));
                DoubleInterval derivedEvalInterval = carl::IntervalEvaluation::evaluate((*_varIcpVarMapIter->second->candidates().begin())->derivative(), tmpIntervals); // TODO: WHY ANY DERIVATIVE??
                if( derivedEvalInterval.lowerBoundType() == carl::BoundType::INFTY || derivedEvalInterval.upperBoundType() == carl::BoundType::INFTY )
                    return std::numeric_limits<double>::infinity();
                impact = derivedEvalInterval.diameter() * originalDiameter;
                break;
            }
            case 3: // Rule of Ratz - minimize width of inclusion
            {
                EvalDoubleIntervalMap tmpIntervals = mIntervals;
                tmpIntervals.insert(std::make_pair(_varIcpVarMapIter->first,DoubleInterval(1)));
                DoubleInterval derivedEvalInterval = carl::IntervalEvaluation::evaluate((*_varIcpVarMapIter->second->candidates().begin())->derivative(), tmpIntervals); // TODO: WHY ANY DERIVATIVE??
                DoubleInterval negCenter = varInterval.inverse();
                negCenter = negCenter.add(varInterval);
                derivedEvalInterval = derivedEvalInterval.mul(negCenter);
                if( derivedEvalInterval.lowerBoundType() == carl::BoundType::INFTY || derivedEvalInterval.upperBoundType() == carl::BoundType::INFTY )
                    return std::numeric_limits<double>::infinity();
                impact = derivedEvalInterval.diameter();
                break;
            }
            case 4: // Select according to optimal machine representation of bounds
            {
                if( varInterval.contains(0) )
                    impact = originalDiameter;
                else
                    impact = originalDiameter/(varInterval.upper() > 0 ? varInterval.lower() : varInterval.upper());
                break;
            }
            default:
            {
                impact = originalDiameter;
                if( varInterval.lowerBoundType() == carl::BoundType::STRICT )
                    impact = std::nextafter( impact, -INFINITY );
                if( varInterval.upperBoundType() == carl::BoundType::STRICT )
                    impact = std::nextafter( impact, -INFINITY );
                break;
            }
        }
        #ifdef ICP_MODULE_DEBUG_1
        std::cout << __PRETTY_FUNCTION__ << " Rule " << mSplittingStrategy << ": " << impact << std::endl;
        #endif
        return impact;
    }

    template<class Settings>
    FormulasT ICPModule<Settings>::createPremiseDeductions()
    {
        // collect applied contractions
        FormulasT contractions = mHistoryActual->appliedConstraints();
        // collect original box
        assert( mBoxStorage.size() > 0 );
        const FormulaSetT& box = mBoxStorage.front();
        contractions.insert(contractions.end(), box.begin(), box.end() );
        mBoxStorage.pop();
        return contractions;
    }

    template<class Settings>
    std::vector<FormulaT> ICPModule<Settings>::createPremise()
    {
        // collect applied contractions
        std::vector<FormulaT> contractions;
        mHistoryActual->appliedConstraints( contractions );
        // collect original box
        assert( mBoxStorage.size() > 0 );
        for( const FormulaT& f : mBoxStorage.front() )
            contractions.push_back( f );
        mBoxStorage.pop();
        return contractions;
    }
    
    template<class Settings>
    FormulaSetT ICPModule<Settings>::createBoxFormula()
    {
        carl::Variables originalRealVariables;
        rReceivedFormula().realValuedVars(originalRealVariables); // TODO: store original variables as member, updating them efficiently with assert and remove
        FormulaSetT subformulas;
        for( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
        {
            if( originalRealVariables.find( (*intervalIt).first ) != originalRealVariables.end() )
            {
                std::pair<ConstraintT, ConstraintT> boundaries = icp::intervalToConstraint(carl::makePolynomial<Poly>((*intervalIt).first), (*intervalIt).second);
                if( boundaries.first != ConstraintT() )
                    subformulas.insert( FormulaT( boundaries.first ) );
                if( boundaries.second != ConstraintT() )
                    subformulas.insert( FormulaT( boundaries.second ) );
            }
        }
        return subformulas;
    }
    
    template<class Settings>
    bool ICPModule<Settings>::performSplit( bool _contractionApplied, bool& _furtherContractionApplied )
    {
        assert( !intervalsEmpty() );
        Rational bound;
        bool leftCaseWeak = true;
        bool preferLeftCase = true;
        carl::Variable variable;
        switch( mSplittingHeuristic )
        {
            case SplittingHeuristic::SIZE:
                sizeBasedSplitting( variable, bound, leftCaseWeak, preferLeftCase );
                break;
            case SplittingHeuristic::UNSATISFIABILITY:
                _furtherContractionApplied = satBasedSplitting( variable, bound, leftCaseWeak, preferLeftCase );
                break;
            case SplittingHeuristic::SATISFIABILITY:
                _furtherContractionApplied = satBasedSplitting( variable, bound, leftCaseWeak, preferLeftCase );
                break;
            default:
                assert(false);
        }
        if( variable != carl::Variable::NO_VARIABLE )
        {
            // create split: (not h_b OR (Not x<b AND x>=b) OR (x<b AND Not x>=b) )
            // first the premise: ((oldBox AND CCs) -> newBox) in CNF: (oldBox OR CCs) OR newBox 
            std::vector<FormulaT> splitPremise = createPremise();
            if( _contractionApplied )
            {
                FormulaSetT subformulas;
                for( auto formulaIt = splitPremise.begin(); formulaIt != splitPremise.end(); ++formulaIt )
                    subformulas.insert( FormulaT( carl::FormulaType::NOT, *formulaIt ) );
                // construct new box
                subformulas.insert( FormulaT( carl::FormulaType::AND, std::move( createBoxFormula() ) ) ); // TODO: only add this deduction if any contraction took place!!!
                // push deduction
                addDeduction( FormulaT( carl::FormulaType::OR, std::move(subformulas) ) );
                #ifdef ICP_MODULE_SHOW_PROGRESS
                addProgress( mInitialBoxSize - calculateCurrentBoxSize() );
                #endif
            }
            assert( variable != carl::Variable::NO_VARIABLE);
            assert( splittings().size() == 0 );
            Module::branchAt( variable, bound, std::move(splitPremise), leftCaseWeak, preferLeftCase );
            #ifdef ICP_MODULE_DEBUG_0
            std::cout << std::endl << "Force split on " << variable << " at " << bound << "!" << std::endl;
            printIntervals(true);
            #endif
            return true;
        }
        return false;
    }
    
    template<class Settings>
    bool ICPModule<Settings>::splitToBoundedIntervalsWithoutZero( carl::Variable& _variable, Rational& _value, bool& _leftCaseWeak, bool& _preferLeftCase )
    {
        double valueAsDouble = 0;
        for( const auto& varIcpvarPair : mVariables )
        {
            const auto& varInterval = varIcpvarPair.second->interval();
            if( varIcpvarPair.second->isOriginal() && varIcpvarPair.second->isActive() && !varInterval.isPointInterval() )
            {
                if( varInterval.upperBoundType() == carl::BoundType::INFTY )
                {
                    if( varInterval.lowerBoundType() != carl::BoundType::INFTY )
                    {
                        // a is finite => if b = mDefaultSplittingSize is not in the interval give up otherwise split to <a,b] and (b,oo)
                        assert( mDefaultSplittingSize > 0 );
                        if( varInterval.lower() < mDefaultSplittingSize )
                        {
                            _variable = varIcpvarPair.first;
                            valueAsDouble = mDefaultSplittingSize;
                            _leftCaseWeak = true;
                            _preferLeftCase = true;
                        }
                    }
                    else // otherwise the interval is (-oo,oo) so keep 0
                    {
                        _variable = varIcpvarPair.first;
                        valueAsDouble = mDefaultSplittingSize;
                        _leftCaseWeak = true;
                        _preferLeftCase = true;
                    }
                    
                }
                else if( varInterval.lowerBoundType() == carl::BoundType::INFTY ) // Variable interval is (-oo,a> and a finite
                {
                    // if b = -mDefaultSplittingSize is not in the interval give up otherwise split to (-oo,b) and [b,a>
                    if( varInterval.upper() <= -mDefaultSplittingSize )
                    {
                        _variable = varIcpvarPair.first;
                        valueAsDouble = -mDefaultSplittingSize;
                        _preferLeftCase = false;
                        _leftCaseWeak = false;
                    }
                }
                else if( varInterval.lowerBoundType() == carl::BoundType::WEAK && varInterval.lower() == 0 )
                {
                    // Variable interval is [0,a> => split it to [0,0] and (0,a> 
                    _variable = varIcpvarPair.first;
                    valueAsDouble = varInterval.lower();
                    _preferLeftCase = true;
                    _leftCaseWeak = true;
                }
                else if( varInterval.upperBoundType() == carl::BoundType::WEAK && varInterval.upper() == 0 )
                {
                    // Variable interval is <a,0] => split it to <a,0) and [0,0]
                    _variable = varIcpvarPair.first;
                    valueAsDouble = varInterval.upper();
                    _preferLeftCase = false;
                    _leftCaseWeak = false;
                }
                if( _variable != carl::Variable::NO_VARIABLE )
                {
                    if( mSplittingHeuristic == SplittingHeuristic::SATISFIABILITY || mSplittingHeuristic == SplittingHeuristic::UNSATISFIABILITY )
                    {
                        FormulaT violatedConstraint;
                        EvalDoubleIntervalMap intervals = mIntervals;
                        intervals[_variable] = DoubleInterval( varInterval.lower(), varInterval.lowerBoundType(), valueAsDouble, (_leftCaseWeak ? carl::BoundType::WEAK : carl::BoundType::STRICT) );
                        if( satBasedSplittingImpact( intervals, violatedConstraint, false ) < 0 )
                        {
                            assert( violatedConstraint.getType() == carl::FormulaType::CONSTRAINT );
                            icp::ContractionCandidate* cc = getContractionCandidate( violatedConstraint, _variable );
                            assert( cc != nullptr );
                            setContraction( cc, *varIcpvarPair.second, varInterval, intervals[_variable] );
                            return true;
                        }
                        intervals[_variable] = DoubleInterval( valueAsDouble, (_leftCaseWeak ? carl::BoundType::STRICT : carl::BoundType::WEAK), varInterval.upper(), varInterval.upperBoundType() );
                        if( satBasedSplittingImpact( intervals, violatedConstraint, false ) < 0 )
                        {
                            assert( violatedConstraint.getType() == carl::FormulaType::CONSTRAINT );
                            icp::ContractionCandidate* cc = getContractionCandidate( violatedConstraint, _variable );
                            assert( cc != nullptr );
                            setContraction( cc, *varIcpvarPair.second, varInterval, intervals[_variable] );
                            return true;
                        }
                    }
                    _value = carl::rationalize<Rational>( valueAsDouble );
                    return false;
                }
            }
        }
        return false;
    }

    template<class Settings>
    void ICPModule<Settings>::sizeBasedSplitting( carl::Variable& _variable, Rational& _value, bool& _leftCaseWeak, bool& _preferLeftCase )
    {
        _value = ZERO_RATIONAL;
        _leftCaseWeak = true;
        _preferLeftCase = true;
        if( Settings::first_split_to_bounded_intervals_without_zero )
        {
            splitToBoundedIntervalsWithoutZero( _variable, _value, _leftCaseWeak, _preferLeftCase );
            if( _variable != carl::Variable::NO_VARIABLE )
                return;
        }
        assert( _variable == carl::Variable::NO_VARIABLE );
        double maximalImpact = 0;
        auto bestVar = mVariables.end();
        auto varIcpvarIter = mVariables.begin();
        for( ; varIcpvarIter != mVariables.end(); ++varIcpvarIter )
        {
            if( !fulfillsTarget(varIcpvarIter->second->interval()) )
            {
                double actualImpact = sizeBasedSplittingImpact( varIcpvarIter );
                if( actualImpact > maximalImpact )
                {
                    bestVar = varIcpvarIter;
                    maximalImpact = actualImpact;
                }
            }
        }
        if( bestVar != mVariables.end() )
        {
            // split at a nice number c in the interval: <a,c] and (c,b> 
            _variable = bestVar->first;
            _value = carl::rationalize<Rational>( bestVar->second->interval().sample( false ) );
        }
        return;
    }

    template<class Settings>
    bool ICPModule<Settings>::satBasedSplitting( carl::Variable& _variable, Rational& _value, bool& _leftCaseWeak, bool& _preferLeftCase )
    {
        _value = ZERO_RATIONAL;
        _leftCaseWeak = true;
        _preferLeftCase = true;
        if( Settings::first_split_to_bounded_intervals_without_zero )
        {
            if( splitToBoundedIntervalsWithoutZero( _variable, _value, _leftCaseWeak, _preferLeftCase ) )
                return true;
            if( _variable != carl::Variable::NO_VARIABLE )
                return false;
        }
        assert( _variable == carl::Variable::NO_VARIABLE );
        _leftCaseWeak = true;
        double valueAsDouble = 0;
        double maximalImpact = -1;
        for( const auto& varIcpvarPair : mVariables )
        {
            const auto& varInterval = varIcpvarPair.second->interval();
            if( fulfillsTarget(varInterval) )
                continue;
            valueAsDouble = varInterval.sample( false );
            bool leftCaseWeak = true;
            if( valueAsDouble == varInterval.upper() )
                leftCaseWeak = false;
            EvalDoubleIntervalMap intervals = mIntervals;
            intervals[varIcpvarPair.first] = DoubleInterval( varInterval.lower(), varInterval.lowerBoundType(), valueAsDouble, leftCaseWeak ? carl::BoundType::WEAK : carl::BoundType::STRICT );
            FormulaT violatedConstraint;
            double impactLeftCase = satBasedSplittingImpact( intervals, violatedConstraint, true );
            if( impactLeftCase < 0 )
            {
                assert( violatedConstraint.getType() == carl::FormulaType::CONSTRAINT );
                icp::ContractionCandidate* cc = getContractionCandidate( violatedConstraint, varIcpvarPair.first );
                assert( cc != nullptr );
                setContraction( cc, *varIcpvarPair.second, varInterval, intervals[varIcpvarPair.first] );
                return true;
            }
            intervals[varIcpvarPair.first] = DoubleInterval( valueAsDouble, leftCaseWeak ? carl::BoundType::STRICT : carl::BoundType::WEAK, varInterval.upper(), varInterval.upperBoundType() );
            double impactRightCase = satBasedSplittingImpact( intervals, violatedConstraint, true );
            if( impactRightCase < 0 )
            {
                assert( violatedConstraint.getType() == carl::FormulaType::CONSTRAINT );
                icp::ContractionCandidate* cc = getContractionCandidate( violatedConstraint, varIcpvarPair.first );
                assert( cc != nullptr );
                setContraction( cc, *varIcpvarPair.second, varInterval, intervals[varIcpvarPair.first] );
                return true;
            }
            if( impactLeftCase > impactRightCase )
            {
                if( impactLeftCase > maximalImpact )
                {
                    maximalImpact = impactLeftCase;
                    _variable = varIcpvarPair.first;
                    _preferLeftCase = true;
                    _value = carl::rationalize<Rational>( valueAsDouble );
                }
            }
            else
            {
                if( impactRightCase > maximalImpact )
                {
                    maximalImpact = impactRightCase;
                    _variable = varIcpvarPair.first;
                    _preferLeftCase = false;
                    _value = carl::rationalize<Rational>( valueAsDouble );
                }
            }
        }
        return false;
    }
    
//    #define ICP_SAT_BASED_SPLITTING_DEBUG
    
    template<class Settings>
    double ICPModule<Settings>::satBasedSplittingImpact( const EvalDoubleIntervalMap& _intervals, FormulaT& _violatedConstraint, bool _calculateImpact ) const
    {
        assert( !intervalsEmpty( _intervals ) );
        assert( mSplittingHeuristic == SplittingHeuristic::SATISFIABILITY || mSplittingHeuristic == SplittingHeuristic::UNSATISFIABILITY );
        double result = 0;
        #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
        std::cout << _intervals << std::endl;
        #endif
        for( const auto& rec : rReceivedFormula() )
        {
            assert( rec.formula().getType() == carl::FormulaType::CONSTRAINT );
            const ConstraintT& constraint = rec.formula().constraint();
            #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
            std::cout << constraint << std::endl;
            #endif
            DoubleInterval solutionSpace = carl::IntervalEvaluation::evaluate( constraint.lhs(), _intervals );
            #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
            std::cout << solutionSpace << std::endl;
            #endif
            switch( constraint.relation() )
            {
                case carl::Relation::EQ:
                    if( solutionSpace.contains( 0 ) )
                    {
                        if( mSplittingHeuristic == SplittingHeuristic::UNSATISFIABILITY )
                        {
                            if( solutionSpace.isUnbounded() )
                            {
                                #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                                std::cout << "Result: " << std::numeric_limits<double>::infinity() << std::endl;
                                #endif
                                return std::numeric_limits<double>::infinity();
                            }
                            if( !_calculateImpact )
                                break;
                            assert( (solutionSpace.diameter()/rReceivedFormula().size()) >= (double) 0 );
                            result += (solutionSpace.diameter()/rReceivedFormula().size());
                        }
                    }
                    else
                    {
                        #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                        std::cout << "Result: -1" << std::endl;
                        #endif
                        _violatedConstraint = rec.formula();
                        return -1;
                    }
                    break;
                case carl::Relation::LEQ:
                    if( solutionSpace > (double)0 )
                    {
                        #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                        std::cout << "Result: -1" << std::endl;
                        #endif
                        _violatedConstraint = rec.formula();
                        return -1;
                    }
                    else
                    {
                        if( mSplittingHeuristic == SplittingHeuristic::SATISFIABILITY )
                        {
                            if( solutionSpace.lowerBoundType() == carl::BoundType::INFTY )
                            {
                                #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                                std::cout << "Result: " << std::numeric_limits<double>::infinity() << std::endl;
                                #endif
                                return std::numeric_limits<double>::infinity();
                            }
                            if( !_calculateImpact )
                                break;
                            if( solutionSpace.upperBoundType() != carl::BoundType::INFTY && solutionSpace.upper() < (double) 0 )
                            {
                                assert( (solutionSpace.diameter()/rReceivedFormula().size()) >= (double) 0 );
                                result += (solutionSpace.diameter()/rReceivedFormula().size());
                            }
                            else
                            {
                                assert( (-solutionSpace.lower()/rReceivedFormula().size()) >= (double) 0 );
                                result += (-solutionSpace.lower()/rReceivedFormula().size());
                            }
                        }
                        else
                        {
                            if( solutionSpace.upperBoundType() == carl::BoundType::INFTY )
                            {
                                #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                                std::cout << "Result: " << std::numeric_limits<double>::infinity() << std::endl;
                                #endif
                                return std::numeric_limits<double>::infinity();
                            }
                            if( !_calculateImpact )
                                break;
                            if( solutionSpace.upper() > (double) 0 )
                            {
                                assert( solutionSpace.lowerBoundType() == carl::BoundType::INFTY || solutionSpace.lower() <= (double) 0 );
                                assert( (solutionSpace.upper()/rReceivedFormula().size()) >= (double) 0 );
                                result += (solutionSpace.upper()/rReceivedFormula().size());
                            }
                        }
                    }
                    break;
                case carl::Relation::GEQ:
                    if( solutionSpace < (double)0 )
                    {
                        #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                        std::cout << "Result: -1" << std::endl;
                        #endif
                        _violatedConstraint = rec.formula();
                        return -1;
                    }
                    else
                    {
                        if( mSplittingHeuristic == SplittingHeuristic::SATISFIABILITY )
                        {
                            if( solutionSpace.upperBoundType() == carl::BoundType::INFTY )
                            {
                                #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                                std::cout << "Result: " << std::numeric_limits<double>::infinity() << std::endl;
                                #endif
                                return std::numeric_limits<double>::infinity();
                            }
                            if( !_calculateImpact )
                                break;
                            if( solutionSpace.lowerBoundType() != carl::BoundType::INFTY && solutionSpace.lower() > (double) 0 )
                            {
                                assert( (solutionSpace.diameter()/rReceivedFormula().size()) >= (double) 0 );
                                result += (solutionSpace.diameter()/rReceivedFormula().size());
                            }
                            else
                            {
                                assert( (solutionSpace.upper()/rReceivedFormula().size()) >= (double) 0 );
                                result += (solutionSpace.upper()/rReceivedFormula().size());
                            }
                        }
                        else
                        {
                            if( solutionSpace.lowerBoundType() == carl::BoundType::INFTY )
                            {
                                #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                                std::cout << "Result: " << std::numeric_limits<double>::infinity() << std::endl;
                                #endif
                                return std::numeric_limits<double>::infinity();
                            }
                            if( !_calculateImpact )
                                break;
                            if( solutionSpace.lower() < (double) 0 )
                            {
                                assert( solutionSpace.upperBoundType() == carl::BoundType::INFTY || solutionSpace.upper() <= (double) 0 );
                                assert( (-solutionSpace.lower()/rReceivedFormula().size()) >= (double) 0 );
                                result += (-solutionSpace.lower()/rReceivedFormula().size());
                            }
                        }
                    }
                    break;
                case carl::Relation::LESS:
                    if( solutionSpace >= (double)0 )
                    {
                        #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                        std::cout << "Result: -1" << std::endl;
                        #endif
                        _violatedConstraint = rec.formula();
                        return -1;
                    }
                    else
                    {
                        if( mSplittingHeuristic == SplittingHeuristic::SATISFIABILITY )
                        {
                            if( solutionSpace.lowerBoundType() == carl::BoundType::INFTY )
                            {
                                #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                                std::cout << "Result: " << std::numeric_limits<double>::infinity() << std::endl;
                                #endif
                                return std::numeric_limits<double>::infinity();
                            }
                            if( !_calculateImpact )
                                break;
                            if( solutionSpace.upperBoundType() != carl::BoundType::INFTY && solutionSpace.upper() < (double) 0 )
                            {
                                assert( (solutionSpace.diameter()/rReceivedFormula().size()) >= (double) 0 );
                                result += (solutionSpace.diameter()/rReceivedFormula().size());
                            }
                            else
                            {
                                assert( (-solutionSpace.lower()/rReceivedFormula().size()) >= (double) 0 );
                                result += (-solutionSpace.lower()/rReceivedFormula().size());
                            }
                        }
                        else
                        {
                            if( solutionSpace.upperBoundType() == carl::BoundType::INFTY )
                            {
                                #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                                std::cout << "Result: " << std::numeric_limits<double>::infinity() << std::endl;
                                #endif
                                return std::numeric_limits<double>::infinity();
                            }
                            if( !_calculateImpact )
                                break;
                            if( solutionSpace.upper() > (double) 0 )
                            {
                                assert( solutionSpace.lowerBoundType() == carl::BoundType::INFTY || solutionSpace.lower() < (double) 0 );
                                assert( (solutionSpace.upper()/rReceivedFormula().size()) >= (double) 0 );
                                result += (solutionSpace.upper()/rReceivedFormula().size());
                            }
                        }
                    }
                    break;
                case carl::Relation::GREATER:
                    if( solutionSpace <= (double)0 )
                    {
                        #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                        std::cout << "Result: -1" << std::endl;
                        #endif
                        _violatedConstraint = rec.formula();
                        return -1;
                    }
                    else
                    {
                        if( mSplittingHeuristic == SplittingHeuristic::SATISFIABILITY )
                        {
                            if( solutionSpace.upperBoundType() == carl::BoundType::INFTY )
                            {
                                #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                                std::cout << "Result: " << std::numeric_limits<double>::infinity() << std::endl;
                                #endif
                                return std::numeric_limits<double>::infinity();
                            }
                            if( !_calculateImpact )
                                break;
                            if( solutionSpace.lowerBoundType() != carl::BoundType::INFTY && solutionSpace.lower() > (double) 0 )
                            {
                                assert( (solutionSpace.diameter()/rReceivedFormula().size()) >= (double) 0 );
                                result += (solutionSpace.diameter()/rReceivedFormula().size());
                            }
                            else
                            {
                                assert( (solutionSpace.upper()/rReceivedFormula().size()) >= (double) 0 );
                                result += (solutionSpace.upper()/rReceivedFormula().size());
                            }
                        }
                        else
                        {
                            if( solutionSpace.lowerBoundType() == carl::BoundType::INFTY )
                            {
                                #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
                                std::cout << "Result: " << std::numeric_limits<double>::infinity() << std::endl;
                                #endif
                                return std::numeric_limits<double>::infinity();
                            }
                            if( !_calculateImpact )
                                break;
                            if( solutionSpace.lower() < (double) 0 )
                            {
                                assert( solutionSpace.upperBoundType() == carl::BoundType::INFTY || solutionSpace.upper() < (double) 0 );
                                assert( (-solutionSpace.lower()/rReceivedFormula().size()) >= (double) 0 );
                                result += (-solutionSpace.lower()/rReceivedFormula().size());
                            }
                        }
                    }
                    break;
                default: // carl::Relation::NEQ
                    // ignore them
                    break;
            }
        }
        #ifdef ICP_SAT_BASED_SPLITTING_DEBUG
        std::cout << "Result: " << result << std::endl;
        #endif
        return result;
    }
    
    template<class Settings>
    bool ICPModule<Settings>::tryTestPoints()
    {
        bool testSuccessful = true;
        // find a point within the intervals
        carl::Variables originalRealVariables;
        rReceivedFormula().realValuedVars(originalRealVariables); // TODO: store original variables as member, updating them efficiently with assert and remove
        std::map<carl::Variable, double> antipoint = createModel( true );
        mFoundSolution.clear();
        #ifdef ICP_MODULE_DEBUG_0
        std::cout << __func__ << ":" << std::endl;
        #endif
        if( antipoint.empty() )
        {
            #ifdef ICP_MODULE_DEBUG_0
            std::cout << "  Failed!" << std::endl << std::endl;
            #endif
            return false;
        }
        bool boxContainsOnlyOneSolution = true;
        auto origVarsIter = originalRealVariables.begin();
        EvalRationalIntervalMap lraVarBounds = mLRA.getVariableBounds();
        for( auto iter = antipoint.begin(); iter != antipoint.end(); ++iter )
        {
            // Add an assignment for variables only occurring in constraints with != as relation symbol
            while( origVarsIter != originalRealVariables.end() && *origVarsIter < iter->first )
            {
                mFoundSolution.insert( std::make_pair( *origVarsIter, ZERO_RATIONAL ) ); // TODO: find a rational assignment which most probably satisfies this inequality
                ++origVarsIter;
            }
            if( origVarsIter != originalRealVariables.end() )
                ++origVarsIter;
            // rationalize the found test point for the given dimension
            Rational value = carl::rationalize<Rational>( iter->second );
            // check if the test point, which has been generated for double intervals, does not satisfy the rational 
            // original bounds in this dimension (might occur, as we over-approximated them)
            auto lraVarBoundsIter = lraVarBounds.find( iter->first );
            if( lraVarBoundsIter != lraVarBounds.end() )
            {
                const RationalInterval& varBounds = lraVarBoundsIter->second;
                assert( !varBounds.isEmpty() );
                if( varBounds.isPointInterval() )
                {
                    value = varBounds.lower();
                }
                else
                {
                    assert( iter->first.getType() != carl::VariableType::VT_INT || varBounds.isUnbounded() || varBounds.diameter() >= ONE_RATIONAL );
                    if( iter->first.getType() != carl::VariableType::VT_INT )
                        boxContainsOnlyOneSolution = false;
                    if( varBounds.lowerBoundType() != carl::BoundType::INFTY && value < varBounds.lower() )
                    {
                        if( varBounds.lowerBoundType() == carl::BoundType::STRICT )
                            value = varBounds.sample( false );
                        else
                            value = varBounds.lower();
                    }
                    else if( varBounds.upperBoundType() != carl::BoundType::INFTY && value > varBounds.upper() )
                    {
                        if( varBounds.upperBoundType() == carl::BoundType::STRICT )
                            value = varBounds.sample( false );
                        else
                            value = varBounds.upper();
                    }
                }
            }
            #ifdef ICP_MODULE_DEBUG_0
            std::cout << "    " << iter->first << " -> " << std::setprecision(10) << iter->second << "  [" << value << "]" << std::endl;
            #endif
            mFoundSolution.insert( std::make_pair( iter->first, value ) );
        }
        for( auto candidate = mActiveNonlinearConstraints.begin(); candidate != mActiveNonlinearConstraints.end(); ++candidate )
        {
            unsigned isSatisfied = (*candidate)->constraint().satisfiedBy( mFoundSolution );
            assert( isSatisfied != 2 );
            if( isSatisfied == 0 )
            {
                testSuccessful = false;
                if( boxContainsOnlyOneSolution )
                {
                    
                }
                break;
            }
        }
        if( testSuccessful )
        {
            for( auto iter = mLinearConstraints.begin(); iter != mLinearConstraints.end(); ++iter )
            {
                assert( !iter->second.empty() );
                unsigned isSatisfied = iter->first->isSatisfiedBy( mFoundSolution );
                assert( isSatisfied != 2 );
                if( isSatisfied == 0 )
                {
                    testSuccessful = false;
                    break;
                }
            }
        }
        if( !testSuccessful )
            mFoundSolution.clear();
        #ifdef ICP_MODULE_DEBUG_0
        if( testSuccessful ) std::cout << "  Success!" << std::endl << std::endl;
        #endif
        return testSuccessful;
    }
    
    template<class Settings>
    bool ICPModule<Settings>::initialLinearCheck( Answer& _answer )
    {
        #ifdef ICP_MODULE_DEBUG_1
        std::cout << "Initial linear check:" << std::endl;
        #endif
        // call mLRA to check linear feasibility
        mLRA.clearDeductions();
        mValidationFormula->updateProperties();
        _answer = mLRA.check();
        
        // catch deductions
        for( const auto& ded : mLRA.deductions() )
        {
            #ifdef ICP_MODULE_DEBUG_2
            std::cout << "Create deduction for: " << ded.first << std::endl;
            #endif
            FormulaT deduction = getReceivedFormulas(ded.first);
            addDeduction(deduction, ded.second);
            #ifdef ICP_MODULE_DEBUG_2   
            std::cout << "Passed deduction: " << deduction << std::endl;
            #endif
        }
        if( Settings::use_lramodules_splitting_decisions )
        {
            for( auto& sp : mLRA.splittings() )
            {
                vector<FormulaT> premise;
                for( const auto& form : sp.mPremise )
                {
                    getOrigins( form, premise );
                    addSplitting( sp.mLeftCase, sp.mRightCase, std::move( premise ), sp.mPreferLeftCase );
                }
            }
        }
        mLRA.clearDeductions();
        if( _answer == False )
        {
            // remap infeasible subsets to original constraints
            remapAndSetLraInfeasibleSubsets();
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "LRA: " << _answer << std::endl;
            #endif
            return true;
        }
        else if( _answer == True && mActiveNonlinearConstraints.empty() ) // _answer == True, but no nonlinear constraints -> linear solution is a solution
        {
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "LRA: " << _answer << std::endl;
            #endif
            mFoundSolution = mLRA.getRationalModel();
            return true;
        }
        else // _answer == True or _answer == Unknown
        {
            if( !splittings().empty() && _answer == Unknown )
                return true;
            // get intervals for initial variables
            EvalRationalIntervalMap tmp = mLRA.getVariableBounds();
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "Newly obtained Intervals: " << std::endl;
            #endif
            for ( auto constraintIt = tmp.begin(); constraintIt != tmp.end(); ++constraintIt )
            {
                #ifdef ICP_MODULE_DEBUG_1
                std::cout << (*constraintIt).first << ": " << (*constraintIt).second << std::endl;
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
                    mHistoryRoot->rIntervals()[(*(*linIt).second.begin())->lhs()] = DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType());
                    // No need to propagate update-status in the icp-variable
                    assert( mIntervals.find( (*(*linIt).second.begin())->lhs() ) != mIntervals.end() );
                    mIntervals[(*(*linIt).second.begin())->lhs()] = DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType());
                    #ifdef ICP_MODULE_DEBUG_2
                    std::cout << "Added interval (slackvariables): " << (*(*linIt).second.begin())->lhs() << " " << tmp << std::endl;
                    #endif
                }
            }
            // temporary solution - an added linear constraint might have changed the box.
            setBox(mHistoryRoot);
            mHistoryRoot->rReasons().clear();
            mHistoryRoot->rStateInfeasibleConstraints().clear();
            mHistoryRoot->rStateInfeasibleVariables().clear();
            #ifdef ICP_MODULE_DEBUG_1
            std::cout << "Id actual box: " << mHistoryActual->id() << " Size subtree: " << mHistoryActual->sizeSubtree() << std::endl;
            #endif
            return false;
        }
    }
    
    template<class Settings>
    bool ICPModule<Settings>::checkBoxAgainstLinearFeasibleRegion()
    {
        FormulaSetT addedBoundaries = createConstraintsFromBounds(mIntervals,false);
        for( auto formulaIt = addedBoundaries.begin(); formulaIt != addedBoundaries.end();  )
        {
            auto res = mValidationFormula->add( *formulaIt );
            if( res.second )
            {
                mLRA.inform( *formulaIt );
                mLRA.add( res.first );
                ++formulaIt;
            }
            else
            {
                formulaIt = addedBoundaries.erase(formulaIt);
            }
        }
        mValidationFormula->updateProperties();
        Answer boxCheck = mLRA.check();
        #ifdef ICP_MODULE_DEBUG_1
        mLRA.print();
        std::cout << "Boxcheck: " << ANSWER_TO_STRING(boxCheck) << std::endl;
        #endif
        #ifdef SMTRAT_DEVOPTION_VALIDATION_ICP
        if ( boxCheck == False )
        {
            FormulaT actualAssumptions = FormulaT(*mValidationFormula);
            Module::addAssumptionToCheck(actualAssumptions,false,"ICP_BoxValidation");
        }
        #endif
        if( boxCheck != Unknown )
        {
            if( boxCheck != True )
            {
                std::vector<FormulasT> tmpSet = mLRA.infeasibleSubsets();
                for ( auto infSetIt = tmpSet.begin(); infSetIt != tmpSet.end(); ++infSetIt )
                {
                    for ( auto formulaIt = (*infSetIt).begin(); formulaIt != (*infSetIt).end(); ++formulaIt )
                    {
                        if( !formulaIt->constraint().isBound() )
                        {
                            mHistoryActual->addInfeasibleConstraint(formulaIt->constraint());
                            for( auto variableIt = formulaIt->constraint().variables().begin(); variableIt != formulaIt->constraint().variables().end(); ++variableIt )
                            {
                                assert( mVariables.find(*variableIt) != mVariables.end() );
                                mHistoryActual->addInfeasibleVariable(mVariables.at(*variableIt));
                            }
                        }
                        else
                        {
                            assert( mVariables.find( *formulaIt->constraint().variables().begin() ) != mVariables.end() );
                            mHistoryActual->addInfeasibleVariable( mVariables.at( *formulaIt->constraint().variables().begin()) );
                        }
                    }
                }
            }
            else if( Settings::prolong_contraction )
            {
                EvalRationalIntervalMap bounds = mLRA.getVariableBounds();
                #ifdef ICP_MODULE_DEBUG_1
                std::cout << "Newly obtained Intervals: " << std::endl;
                #endif
                for ( auto boundIt = bounds.begin(); boundIt != bounds.end(); ++boundIt )
                {
                    assert( mVariables.find((*boundIt).first) != mVariables.end() );
                    icp::IcpVariable& icpVar = *mVariables.find((*boundIt).first)->second;
                    RationalInterval tmp = (*boundIt).second;
                    const DoubleInterval& icpVarInterval = icpVar.interval();
                    // mHistoryRoot->addInterval((*boundIt).first, DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType()) );
                    DoubleInterval newInterval = DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType() );
                    if( !(icpVarInterval == newInterval) && icpVarInterval.contains(newInterval) )
                    {
                        #ifdef ICP_MODULE_DEBUG_1
                        std::cout << (*boundIt).first << ": " << (*boundIt).second << std::endl;
                        #endif
                        updateRelativeContraction( icpVarInterval, newInterval );
                        icpVar.setInterval( newInterval );
                        updateRelevantCandidates((*boundIt).first);
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
                        // mHistoryRoot->rIntervals()[(*(*linIt).second.begin())->lhs()] = DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType());
                        DoubleInterval newInterval = DoubleInterval(tmp.lower(), tmp.lowerBoundType(), tmp.upper(), tmp.upperBoundType() );
                        carl::Variable var = (*(*linIt).second.begin())->lhs();
                        icp::IcpVariable& icpVar = *mVariables.at(var);
                        const DoubleInterval& icpVarInterval = icpVar.interval();
                        if( !(icpVarInterval == newInterval) && icpVarInterval.contains(newInterval) )
                        {
                            updateRelativeContraction( icpVarInterval, newInterval );
                            icpVar.setInterval( newInterval );
                            updateRelevantCandidates(var);
                            #ifdef ICP_MODULE_DEBUG_2
                            std::cout << "Added interval (slackvariables): " << var << " " << tmp << std::endl;
                            #endif
                        }
                    }
                }
            }
        }
        // remove boundaries from mLRA module after boxChecking.
        for( auto boundIt = addedBoundaries.begin(); boundIt != addedBoundaries.end(); )
        {
            auto pos = mValidationFormula->find( *boundIt );
            if( pos != mValidationFormula->end() )
            {
                mLRA.remove( pos );
                mValidationFormula->erase( pos );
            }
            boundIt = addedBoundaries.erase(boundIt);
        }
        
        mLRA.clearDeductions();
        assert(addedBoundaries.empty());
        
        if ( boxCheck == False )
            return false;
        return true;
    }

    template<class Settings>
    void ICPModule<Settings>::pushBoundsToPassedFormula()
    {
        carl::Variables originalRealVariables;
        rReceivedFormula().realValuedVars( originalRealVariables ); // TODO: store original variables as member, updating them efficiently with assert and remove
        EvalRationalIntervalMap lraVarBounds = mLRA.getVariableBounds();
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
                    auto lraVarBoundsIter = lraVarBounds.find( tmpSymbol );
                    
                    icp::Updated icpVarExUpdated = icpVar.isExternalUpdated();
                    // generate both bounds, left first
                    if( icpVarExUpdated == icp::Updated::BOTH || icpVarExUpdated == icp::Updated::LEFT )
                    {
                        Rational bound = carl::rationalize<Rational>( interval.lower() );
                        carl::BoundType boundType = interval.lowerBoundType();
                        if( lraVarBoundsIter != lraVarBounds.end() )
                        {
                            const RationalInterval& varBounds = lraVarBoundsIter->second;
                            if( varBounds.lowerBoundType() != carl::BoundType::INFTY && bound < varBounds.lower() )
                            {
                                bound = varBounds.lower();
                                boundType = varBounds.lowerBoundType();
                            }
                        }
                        Poly leftEx = carl::makePolynomial<Poly>( tmpSymbol ) - Poly(bound);

                        FormulaT leftTmp = FormulaT( carl::FormulaType::TRUE );
                        switch( boundType )
                        {
                            case carl::BoundType::STRICT:
                                leftTmp = FormulaT( leftEx, carl::Relation::GREATER );
                                break;
                            case carl::BoundType::WEAK:
                                leftTmp = FormulaT( leftEx, carl::Relation::GEQ );
                                break;
                            default:
                                break;
                        }
                        if( icpVar.externalLeftBound() != passedFormulaEnd() )
                        {
                            Module::eraseSubformulaFromPassedFormula( icpVar.externalLeftBound(), true );
                        }
                        if ( leftTmp.isTrue() )
                        {
                            icpVar.setExternalLeftBound( passedFormulaEnd() );
                        }
                        else
                        {
                            addConstraintToInform( leftTmp );
                            auto res = addSubformulaToPassedFormula( leftTmp );
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
                        carl::BoundType boundType = interval.upperBoundType();
                        if( lraVarBoundsIter != lraVarBounds.end() )
                        {
                            const RationalInterval& varBounds = lraVarBoundsIter->second;
                            if( varBounds.upperBoundType() != carl::BoundType::INFTY && bound > varBounds.upper() )
                            {
                                bound = varBounds.upper();
                                boundType = varBounds.upperBoundType();
                            }
                        }
                        Poly rightEx = carl::makePolynomial<Poly>( tmpSymbol ) - Poly( bound );
                        FormulaT rightTmp = FormulaT( carl::FormulaType::TRUE );
                        switch( boundType )
                        {
                            case carl::BoundType::STRICT:
                                rightTmp = FormulaT( rightEx, carl::Relation::LESS );
                                break;
                            case carl::BoundType::WEAK:
                                rightTmp = FormulaT( rightEx, carl::Relation::LEQ );
                                break;
                            default:
                                break;
                        }
                        if( icpVar.externalRightBound() != passedFormulaEnd() )
                        {
                            Module::eraseSubformulaFromPassedFormula( icpVar.externalRightBound(), true );
                        }
                        if( rightTmp.isTrue() )
                        {
                            icpVar.setExternalRightBound( passedFormulaEnd() );
                        }
                        else
                        {
                            addConstraintToInform( rightTmp );
                            auto res = addSubformulaToPassedFormula( rightTmp );
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
    
    template<class Settings>
    FormulaSetT ICPModule<Settings>::variableReasonHull( icp::set_icpVariable& _reasons )
    {
        FormulaSetT reasons;
        for( auto variableIt = _reasons.begin(); variableIt != _reasons.end(); ++variableIt )
        {
            if ((*variableIt)->lraVar() != nullptr)
            {
                FormulasT definingOriginsTmp = (*variableIt)->lraVar()->getDefiningOrigins();
                FormulasT definingOrigins;
                for( auto& f : definingOriginsTmp )
                {
                    if( rReceivedFormula().contains( f ) )
                        collectOrigins( f, definingOrigins );
                }
                for( auto formulaIt = definingOrigins.begin(); formulaIt != definingOrigins.end(); ++formulaIt )
                {
                    // std::cout << "Defining origin: " << **formulaIt << " FOR " << *(*variableIt) << std::endl;
                    bool hasAdditionalVariables = false;
                    carl::Variables realValuedVars;
                    rReceivedFormula().realValuedVars(realValuedVars); // TODO: store original variables as member, updating them efficiently with assert and remove
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
                        // std::cout << "Addidional variables." << std::endl;
                        for( auto receivedFormulaIt = rReceivedFormula().begin(); receivedFormulaIt != rReceivedFormula().end(); ++receivedFormulaIt )
                        {
                            if( receivedFormulaIt->formula().constraint().hasVariable((*variableIt)->var()) && receivedFormulaIt->formula().constraint().isBound() )
                            {
                                reasons.insert( receivedFormulaIt->formula() );
                                // std::cout << "Also add: " << **receivedFormulaIt << std::endl;
                            }
                        }
                    }
                    else
                    {
                        // std::cout << "No additional variables." << std::endl;
                        auto replacementIt = mDeLinearizations.find( *formulaIt );
                        assert( replacementIt != mDeLinearizations.end() ); // TODO (from Florian): Do we need this?
                        reasons.insert((*replacementIt).second);
                    } // has no additional variables
                } // for all definingOrigins
            }
        }
        return reasons;
    }
    
    template<class Settings>
    FormulaSetT ICPModule<Settings>::constraintReasonHull( const std::set<ConstraintT>& _reasons )
    {
        FormulaSetT reasons;
        for ( auto constraintIt = _reasons.begin(); constraintIt != _reasons.end(); ++constraintIt )
        {
            for ( auto formulaIt = rReceivedFormula().begin(); formulaIt != rReceivedFormula().end(); ++formulaIt )
            {
                if ( *constraintIt == formulaIt->formula().constraint() )
                {
                    reasons.insert( formulaIt->formula() );
                    break;
                }
            }
        }
        return reasons;
    }
    
    template<class Settings>
    FormulaSetT ICPModule<Settings>::createConstraintsFromBounds( const EvalDoubleIntervalMap& _map, bool _onlyOriginals )
    {
        FormulaSetT addedBoundaries;
        for ( auto variablesIt = mVariables.begin(); variablesIt != mVariables.end(); ++variablesIt )
        {
            if( (_onlyOriginals && !variablesIt->second->isOriginal()) || !variablesIt->second->isActive() )
                continue;
            carl::Variable tmpSymbol = variablesIt->first;
            if ( _map.find(tmpSymbol) != _map.end() )
            {
                if( variablesIt->second->lraVar() != nullptr )
                {
                    std::pair<ConstraintT, ConstraintT> boundaries = icp::intervalToConstraint(carl::makePolynomial<Poly>(variablesIt->second->lraVar()->expression()), _map.at(tmpSymbol));
                    if( boundaries.second != ConstraintT() )
                    {
                        assert( boundaries.second.isConsistent() == 2 );
                        FormulaT rightBound = FormulaT(boundaries.second);
                        addedBoundaries.insert(rightBound);
                        #ifdef ICP_MODULE_DEBUG_2
                        std::cout << "Created upper boundary constraint: " << rightBound << std::endl;
                        #endif
                    }
                    if( boundaries.first != ConstraintT() )
                    {
                        assert( boundaries.first.isConsistent() == 2 );
                        FormulaT leftBound = FormulaT(boundaries.first);
                        addedBoundaries.insert(leftBound);
                        #ifdef ICP_MODULE_DEBUG_2
                        std::cout << "Created lower boundary constraint: " << leftBound << std::endl;
                        #endif
                    }
                }
//                if( (*variablesIt).second->isInternalBoundsSet() == icp::Updated::BOTH && (*variablesIt).second->isInternalUpdated() == icp::Updated::NONE )
//                {
//                    addedBoundaries.insert((*variablesIt).second->internalLeftBound());
//                    addedBoundaries.insert((*variablesIt).second->internalRightBound());
//                }
//                else if( variablesIt->second->lraVar() != nullptr )
//                {
//                    std::pair<ConstraintT, ConstraintT> boundaries = icp::intervalToConstraint(carl::makePolynomial<Poly>(variablesIt->second->lraVar()->expression()), _map.at(tmpSymbol));
//                    icp::Updated inBoundsSet = (*variablesIt).second->isInternalBoundsSet();
//                    icp::Updated inBoundsUpdated = (*variablesIt).second->isInternalUpdated();
//                    if( boundaries.second != ConstraintT() && 
//                        (inBoundsUpdated == icp::Updated::BOTH || inBoundsUpdated == icp::Updated::RIGHT || inBoundsSet == icp::Updated::NONE || inBoundsSet == icp::Updated::LEFT) )
//                    {
//                        assert( boundaries.second.isConsistent() == 2 );
//                        FormulaT rightBound = FormulaT(boundaries.second);
//                        (*variablesIt).second->setInternalRightBound(rightBound);
//                        addedBoundaries.insert(rightBound);
//                        #ifdef ICP_MODULE_DEBUG_2
//                        std::cout << "Created upper boundary constraint: " << rightBound << std::endl;
//                        #endif
//                    }
//                    if( boundaries.first != ConstraintT() && 
//                        (inBoundsUpdated == icp::Updated::BOTH || inBoundsUpdated == icp::Updated::LEFT || inBoundsSet == icp::Updated::NONE || inBoundsSet == icp::Updated::RIGHT) )
//                    {
//                        assert( boundaries.first.isConsistent() == 2 );
//                        FormulaT leftBound = FormulaT(boundaries.first);
//                        (*variablesIt).second->setInternalLeftBound(leftBound);
//                        addedBoundaries.insert(leftBound);
//                        #ifdef ICP_MODULE_DEBUG_2
//                        std::cout << "Created lower boundary constraint: " << leftBound << std::endl;
//                        #endif
//                    }
//                }
            }
        }
        return addedBoundaries;
    }
    
    template<class Settings>
    FormulaT ICPModule<Settings>::getReceivedFormulas( const FormulaT& _deduction )
    {
        if( _deduction.getType() == carl::FormulaType::CONSTRAINT )
        {
            auto iter = mDeLinearizations.find( _deduction );
            if( iter == mDeLinearizations.end() )
            {
                const ConstraintT& c = _deduction.constraint();
                return FormulaT( c.lhs().substitute(mSubstitutions), c.relation() );
            } 
            else
            {
                return iter->second;
            }
        }
        else if( _deduction.getType() == carl::FormulaType::NOT )
        {
            return FormulaT( carl::FormulaType::NOT, getReceivedFormulas( _deduction.subformula() ) );
        }
        else if( _deduction.isBooleanCombination() )
        {
            FormulaSetT subformulas;
            for( const FormulaT& subformula : _deduction.subformulas() )
            {
                subformulas.insert( getReceivedFormulas( subformula ) );
            }
            return FormulaT( _deduction.getType(), subformulas );
        }
        else
        {
            //should not happen
            assert(false);
            return FormulaT( carl::FormulaType::TRUE );
        }
    }
    
    template<class Settings>
    void ICPModule<Settings>::remapAndSetLraInfeasibleSubsets()
    {
        std::vector<FormulasT> tmpSet = mLRA.infeasibleSubsets();
        for ( auto infSetIt = tmpSet.begin(); infSetIt != tmpSet.end(); ++infSetIt )
        {
            FormulasT newSet;
            for( auto formulaIt = (*infSetIt).begin(); formulaIt != (*infSetIt).end(); ++formulaIt )
            {
                auto delinIt = mDeLinearizations.find(*formulaIt);
                assert( delinIt != mDeLinearizations.end() );
                if( rReceivedFormula().contains( delinIt->second ) )
                {
                    newSet.push_back( delinIt->second );
                }
            }
            assert(newSet.size() == (*infSetIt).size());
            mInfeasibleSubsets.push_back(newSet);
        }
    }
    
    template<class Settings>
    double ICPModule<Settings>::calculateCurrentBoxSize()
    {
        if( mIntervals.empty() ) return 0.0;
        double result = 1.0;
        for( const auto& interv : mIntervals )
        {
            auto varIt = mVariables.find(interv.first);
            if( varIt != mVariables.end() && varIt->second->isOriginal() )
            {
                result *= interv.second.diameter();
            }
        }
        return result;
    }
    
    template<class Settings>
    void ICPModule<Settings>::addProgress( double _progress )
    {
        if( _progress > 0.0 )
        {
            mCovererdRegionSize += _progress;
            std::cout << "\r";
            std::cout << std::setprecision(10) << std::setw(20) << (mCovererdRegionSize > 0 ? ((mCovererdRegionSize/mGlobalBoxSize)*100.0) : 0.0) << " %";
            std::cout.flush();
        }
    }

    template<class Settings>
    void ICPModule<Settings>::setBox( icp::HistoryNode* _selection )
    {
        assert(_selection != nullptr);
        #ifdef ICP_MODULE_DEBUG_1
        std::cout << "Set box -> " << _selection->id() << ", #intervals: " << mIntervals.size() << " -> " << _selection->intervals().size() << std::endl;
        #endif
        // set intervals - currently we don't change not contained intervals.
        for ( auto constraintIt = _selection->rIntervals().begin(); constraintIt != _selection->rIntervals().end(); ++constraintIt )
        {
            assert(mIntervals.find((*constraintIt).first) != mIntervals.end());
            // only update intervals which changed
            if ( !(mIntervals.at((*constraintIt).first)==(*constraintIt).second) )
            {
                std::map<carl::Variable, icp::IcpVariable*>::const_iterator icpVar = mVariables.find((*constraintIt).first);
                // std::cout << "Searching for " << (*intervalIt).first.get_name() << std::endl;
                assert(icpVar != mVariables.end());
                (*icpVar).second->setInterval( (*constraintIt).second );
            }
        }
        // set actual node as selection
        mHistoryActual = _selection;
    }
    
    template<class Settings>
    bool ICPModule<Settings>::intervalsEmpty( const EvalDoubleIntervalMap& _intervals ) const
    {
        for( const auto& interval : _intervals )
        {
            if( interval.second.isEmpty() ) return true;
        }
        return false;
    }
    
    template<class Settings>
    bool ICPModule<Settings>::intervalsEmpty( bool _original ) const
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
    
    template<class Settings>
    void ICPModule<Settings>::debugPrint() const
    {
        std::cout << "********************* linear Constraints **********************" << std::endl;
        for( auto linearIt = mLinearConstraints.begin(); linearIt != mLinearConstraints.end(); ++linearIt){
            for ( auto candidateIt = (*linearIt).second.begin(); candidateIt != (*linearIt).second.end(); ++candidateIt )
            {
                std::cout << (*candidateIt)->id() << ": " << (*candidateIt)->constraint() << std::endl;
            }
        }
        std::cout << "****************** active linear constraints ******************" << std::endl;
        for(auto activeLinearIt = mActiveLinearConstraints.begin(); activeLinearIt != mActiveLinearConstraints.end(); ++activeLinearIt){
            std::cout << "Count: " << (*activeLinearIt)->activity() << " , ";
            (*activeLinearIt)->print();
        }
        std::cout << "******************* active linear variables *******************" << std::endl;
        for (auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt )
        {
            if ( (*variableIt).second->isLinear() )
                std::cout << (*variableIt).first << ", ";
        }
        std::cout << std::endl;
        std::cout << "******************** nonlinear constraints ********************" << std::endl;
        ContractionCandidates::iterator replacementsIt;
        for(auto nonlinearIt = mNonlinearConstraints.begin(); nonlinearIt != mNonlinearConstraints.end(); ++nonlinearIt){
            std::cout << (*nonlinearIt).first << std::endl;
            std::cout << "\t replacements: " << std::endl;
            for(replacementsIt = nonlinearIt->second.begin(); replacementsIt != nonlinearIt->second.end(); ++replacementsIt)
            {
                std::cout << "   ";
                (*replacementsIt)->print();
            }
        }
        std::cout << "**************** active nonlinear constraints *****************" << std::endl;
        for( auto activeNonlinearIt = mActiveNonlinearConstraints.begin(); activeNonlinearIt != mActiveNonlinearConstraints.end(); ++activeNonlinearIt )
        {
            std::cout << "Count: " << (*activeNonlinearIt)->activity() << " , ";
            (*activeNonlinearIt)->print();
        }
        std::cout << "***************** active nonlinear variables ******************" << std::endl;
        for (auto variableIt = mVariables.begin(); variableIt != mVariables.end(); ++variableIt )
        {
            if ( (*variableIt).second->isLinear() )
                std::cout << (*variableIt).first << ", ";
        }
        std::cout << std::endl;
        std::cout << "************************** Intervals **************************" << std::endl;
        for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
        {
            std::cout << (*constraintIt).first << "  \t -> \t" << (*constraintIt).second << std::endl;
        }
        std::cout << std::endl;
        std::cout << "************************* Linearizations ************************" << std::endl;
        for ( auto replacementIt = mLinearizations.begin(); replacementIt != mLinearizations.end(); ++replacementIt )
        {
            std::cout << (*replacementIt).first << "  \t -> \t" << (*replacementIt).second << std::endl;
        }
        std::cout <<endl;
        std::cout << "************************* Delinearizations ************************" << std::endl;
        for ( auto replacementIt = mDeLinearizations.begin(); replacementIt != mDeLinearizations.end(); ++replacementIt )
        {
            std::cout << (*replacementIt).first << "  \t -> \t" << (*replacementIt).second << std::endl;
        }
        std::cout <<endl;
        std::cout << "************************* ICP carl::Variables ***********************" << std::endl;
        for ( auto variablesIt = mVariables.begin(); variablesIt != mVariables.end(); ++variablesIt )
            (*variablesIt).second->print( std::cout, true );
        
        std::cout << std::endl;
        std::cout << "*********************** ValidationFormula *********************" << std::endl;
        std::cout << mValidationFormula->toString() << std::endl;
        std::cout << "***************************************************************" << std::endl;
        
        std::cout << "************************* Substitution ************************" << std::endl;
        for( auto subsIt = mSubstitutions.begin(); subsIt != mSubstitutions.end(); ++subsIt )
            std::cout << (*subsIt).first << " -> " << (*subsIt).second << std::endl;
        
        std::cout << "***************************************************************" << std::endl;
    }
    
    template<class Settings>
    void ICPModule<Settings>::printAffectedCandidates() const
    {
        for ( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
        {
            for ( auto candidateIt = (*varIt).second->candidates().begin(); candidateIt != (*varIt).second->candidates().end(); ++candidateIt)
            {
                std::cout << (*varIt).first << "\t -> ";
                (*candidateIt)->print();
            }
        }
    }

    template<class Settings>
    void ICPModule<Settings>::printIcpVariables() const
    {
        for ( auto varIt = mVariables.begin(); varIt != mVariables.end(); ++varIt )
            (*varIt).second->print( std::cout, true );
    }

    template<class Settings>
    void ICPModule<Settings>::printIcpRelevantCandidates() const
    {
        std::cout << "Size icpRelevantCandidates: " << mIcpRelevantCandidates.size() << std::endl;
        for ( auto candidateIt = mIcpRelevantCandidates.begin(); candidateIt != mIcpRelevantCandidates.end(); ++candidateIt )
        {
            std::cout << (*candidateIt).first << " \t " << (*candidateIt).second <<"\t Candidate: ";
            icp::ContractionCandidate* cc = mCandidateManager.getCandidate((*candidateIt).second);
            assert( cc != nullptr );
            cc->print();
        }
    }

    template<class Settings>
    void ICPModule<Settings>::printIntervals( bool _original ) const
    {
        for ( auto constraintIt = mIntervals.begin(); constraintIt != mIntervals.end(); ++constraintIt )
        {
            auto varIt = mVariables.find((*constraintIt).first);
            //assert( varIt != mVariables.end() );//TODO (from FLorian): can we assume this?
            if( !_original || (varIt != mVariables.end() && varIt->second->isOriginal()))
            {
                std::cout << std::setw(10) << (*constraintIt).first;
                std::stringstream s;
                s << (*constraintIt).second;
                std::cout << ":" << std::setw(30) << s.str();
                std::cout << std::endl;
            }
        }
    }
    
    template<class Settings>
    void ICPModule<Settings>::printPreprocessedInput( std::string _init ) const
    {
        ConstraintT last = ConstraintT();
        for(auto activeLinearIt = mActiveLinearConstraints.begin(); activeLinearIt != mActiveLinearConstraints.end(); ++activeLinearIt){
            if( (*activeLinearIt)->constraint() != last )
            {
                last = (*activeLinearIt)->constraint();
                std::cout << _init << last << std::endl;
            }
        }
        last = ConstraintT();
        for(auto activeNoninearIt = mActiveNonlinearConstraints.begin(); activeNoninearIt != mActiveNonlinearConstraints.end(); ++activeNoninearIt){
            if( (*activeNoninearIt)->constraint() != last )
            {
                last = (*activeNoninearIt)->constraint();
                std::cout << _init << last << std::endl;
            }
        }
    }
    
    template<class Settings>
    void ICPModule<Settings>::printContraction( const icp::ContractionCandidate& _cc, const DoubleInterval& _before, const DoubleInterval& _afterA, const DoubleInterval& _afterB, std::ostream& _out ) const
    {
        _out << ((mRelativeContraction > 0 || mAbsoluteContraction > 0) ? "#" : " ");
        _out << std::setw(10) << _cc.derivationVar();
        std::stringstream s;
        s << _before;
        _out << ":" << std::setw(20) << s.str();
        std::stringstream s2;
        if( _afterB.isEmpty() )
        {
            s2 << _afterA;
        }
        else
        {
            s2 << _afterA << " or " << _afterB;
        }
        _out << "  ->  " << std::setw(20) << std::left << s2.str();
        _out << std::right << " with " << _cc.rhs() << std::endl;
    }
} // namespace smtrat
