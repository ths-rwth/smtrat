/**
 * File:   VSModule.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2010-05-11
 * @version 2014-11-27
 */


#include "VSModule.h"

#include <carl-arith/vs/Substitution.h>
#include <carl-arith/vs/Evaluation.h>

#ifdef VS_STATE_DEBUG_METHODS
//#define VS_DEBUG_METHODS
#endif
//#define VS_DEBUG
//#define VS_MODULE_VERBOSE_INTEGERS

namespace smtrat
{

	using namespace vs;
    template<class Settings>
    VSModule<Settings>::VSModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* const _manager ):
        Module( _formula, _conditionals, _manager ),
        mConditionsChanged( false ),
        mInconsistentConstraintAdded( false ),
        mLazyMode( false ),
        mIDCounter( 0 ),
        mLazyCheckThreshold( Settings::lazy_check_threshold ),
        mpConditionIdAllocator(new carl::IDPool() ),
        mpStateTree( new State( mpConditionIdAllocator, Settings::use_variable_bounds ) ),
        mAllVariables(),
        mFormulaConditionMap(),
        mRanking(),
        mVariableVector()
    {
        #ifdef SMTRAT_DEVOPTION_Statistics
        mpStateTree->setStatistics( &mStatistics );
        #endif
    }

    template<class Settings>
    VSModule<Settings>::~VSModule()
    {
        while( !mFormulaConditionMap.empty() )
        {
            const vs::Condition* pRecCond = mFormulaConditionMap.begin()->second;
            mFormulaConditionMap.erase( mFormulaConditionMap.begin() );
            mpConditionIdAllocator->free( pRecCond->id() );
            delete pRecCond;
            pRecCond = NULL;
        }
        delete mpStateTree;
        delete mpConditionIdAllocator;
    }

    template<class Settings>
    bool VSModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        mLazyMode = false;
        bool negated = false;
        FormulaT constraintF = _subformula->formula();
        if( constraintF.type() == carl::FormulaType::NOT && constraintF.subformula().type() == carl::FormulaType::CONSTRAINT )
        {
            constraintF = _subformula->formula().subformula();
            negated = true;
        }
        if( constraintF.type() == carl::FormulaType::CONSTRAINT )
        {
            const ConstraintT& constraint = negated ? ConstraintT( constraintF.constraint().lhs(), carl::inverse( constraintF.constraint().relation() ) ) : constraintF.constraint();
            const vs::Condition* condition = new vs::Condition( constraint, mpConditionIdAllocator->get() );
            mFormulaConditionMap[constraintF] = condition;
            assert( constraint.is_consistent() == 2 );
            for( auto var: constraint.variables() )
                mAllVariables.insert( var );
            if( Settings::incremental_solving )
            {
                removeStatesFromRanking( *mpStateTree );
                mIDCounter = 0;
                carl::PointerSet<vs::Condition> oConds;
                oConds.insert( condition );
                std::vector<DisjunctionOfConditionConjunctions> subResults;
                DisjunctionOfConditionConjunctions subResult;

                if( Settings::split_neq_constraints && constraint.hasIntegerValuedVariable() && !constraint.hasRealValuedVariable() && constraint.relation() == carl::Relation::NEQ )
                {
                    ConditionList condVectorA;
                    condVectorA.push_back( new vs::Condition( ConstraintT( constraint.lhs(), carl::Relation::LESS ), mpConditionIdAllocator->get(), 0, false, oConds ) );
                    subResult.push_back( std::move(condVectorA) );
                    ConditionList condVectorB;
                    condVectorB.push_back( new vs::Condition( ConstraintT( constraint.lhs(), carl::Relation::GREATER ), mpConditionIdAllocator->get(), 0, false, oConds ) );
                    subResult.push_back( std::move(condVectorB) );
                }
                else
                {
                    ConditionList condVector;
                    condVector.push_back( new vs::Condition( constraint, mpConditionIdAllocator->get(), 0, false, oConds ) );
                    subResult.push_back( std::move(condVector) );
                }
                subResults.push_back( std::move(subResult) );
                mpStateTree->addSubstitutionResults( std::move(subResults) );
                addStateToRanking( mpStateTree );
                insertTooHighDegreeStatesInRanking( mpStateTree );
            }
            mConditionsChanged = true;
        }
        else if( _subformula->formula().type() == carl::FormulaType::FALSE )
        {
            removeStatesFromRanking( *mpStateTree );
            mIDCounter = 0;
            mInfeasibleSubsets.clear();
            mInfeasibleSubsets.emplace_back();
            mInfeasibleSubsets.back().insert( _subformula->formula() );
            #ifdef SMTRAT_DEVOPTION_Statistics
            mStatistics.addConflict( rReceivedFormula(), mInfeasibleSubsets );
            #endif
            mInconsistentConstraintAdded = true;
            assert( checkRanking() );
            return false;
        }
        assert( checkRanking() );
        return true;
    }

    template<class Settings>
    void VSModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        mLazyMode = false;
        FormulaT constraintF = _subformula->formula();
        if( constraintF.type() == carl::FormulaType::NOT && constraintF.subformula().type() == carl::FormulaType::CONSTRAINT )
            constraintF = _subformula->formula().subformula();
        if( constraintF.type() == carl::FormulaType::CONSTRAINT )
        {
            mInconsistentConstraintAdded = false;
            auto formulaConditionPair = mFormulaConditionMap.find( constraintF );
            assert( formulaConditionPair != mFormulaConditionMap.end() );
            const vs::Condition* condToDelete = formulaConditionPair->second;
            if( Settings::incremental_solving )
            {
                removeStatesFromRanking( *mpStateTree );
                mpStateTree->rSubResultsSimplified() = false;
                carl::PointerSet<vs::Condition> condsToDelete;
                condsToDelete.insert( condToDelete );
                mpStateTree->deleteOrigins( condsToDelete, mRanking );
                mpStateTree->rType() = State::COMBINE_SUBRESULTS;
                if( mpStateTree->hasSubResultsCombination() )
                    mpStateTree->rTakeSubResultCombAgain() = true;
                else
                    mpStateTree->rTakeSubResultCombAgain() = false;
                addStateToRanking( mpStateTree );
                insertTooHighDegreeStatesInRanking( mpStateTree );
            }
            mFormulaConditionMap.erase( formulaConditionPair );
            mpConditionIdAllocator->free( condToDelete->id() );
            delete condToDelete;
            condToDelete = NULL;
            mConditionsChanged = true;
        }
    }

    template<class Settings>
    Answer VSModule<Settings>::checkCore()
    {
		SMTRAT_LOG_DEBUG("smtrat.vs", "Starting checkCore()");
        #ifdef SMTRAT_DEVOPTION_Statistics
        mStatistics.check();
        #endif
        if( !Settings::incremental_solving )
        {
			SMTRAT_LOG_DEBUG("smtrat.vs", "Do not solve incrementally");
            removeStatesFromRanking( *mpStateTree );
            delete mpStateTree;
            mpStateTree = new State( mpConditionIdAllocator, Settings::use_variable_bounds );
            #ifdef SMTRAT_DEVOPTION_Statistics
            mpStateTree->setStatistics( &mStatistics );
            #endif
            for( auto iter = mFormulaConditionMap.begin(); iter != mFormulaConditionMap.end(); ++iter )
            {
                carl::PointerSet<vs::Condition> oConds;
                oConds.insert( iter->second );
                std::vector<DisjunctionOfConditionConjunctions> subResults;
                subResults.emplace_back();
                subResults.back().emplace_back();
                subResults.back().back().push_back( new vs::Condition( iter->first.constraint(), mpConditionIdAllocator->get(), 0, false, oConds ) );
                mpStateTree->addSubstitutionResults( std::move(subResults) );
            }
            addStateToRanking( mpStateTree );
        }
        if( !rReceivedFormula().isConstraintLiteralConjunction() ) {
            SMTRAT_LOG_DEBUG("smtrat.vs", "Is not a conjunction of literals, return unknown.");
            return UNKNOWN;
        }
        if( !(rReceivedFormula().isIntegerConstraintLiteralConjunction() || rReceivedFormula().isRealConstraintLiteralConjunction()) ) {
            SMTRAT_LOG_DEBUG("smtrat.vs", "Is not purely real or integer, return unknown.");
            return UNKNOWN;
        }
        if( !mFinalCheck && !mConditionsChanged && (!mFullCheck || mLastCheckFull) )
        {
			SMTRAT_LOG_DEBUG("smtrat.vs", "Do not perform a proper check, exit quickly");
            if( mInfeasibleSubsets.empty() )
            {
                if( solverState() == SAT )
                {
                    if( !solutionInDomain() )
                    {
                        return UNKNOWN;
                    }
                    else
                    {
                        return consistencyTrue();
                    }
                }
                else
                {
                    return (mFormulaConditionMap.empty() ? consistencyTrue() : UNKNOWN );
                }
            }
            else
                return UNSAT;
        }
        mConditionsChanged = false;
        mLastCheckFull = mFullCheck;
        if( rReceivedFormula().empty() )
        {
			SMTRAT_LOG_DEBUG("smtrat.vs", "Received formula is empty");
            if( !solutionInDomain() )
            {
                return UNKNOWN;
            }
            else
            {
                return consistencyTrue();
            }
        }
        if( mInconsistentConstraintAdded )
        {
			SMTRAT_LOG_DEBUG("smtrat.vs", "Inconsistent constraint was found");
            assert( !mInfeasibleSubsets.empty() );
            assert( !mInfeasibleSubsets.back().empty() );
            return UNSAT;
        }
        if( Settings::use_variable_bounds )
        {
			SMTRAT_LOG_DEBUG("smtrat.vs", "Trying to employ variable bounds");
            if( !mpStateTree->variableBounds().isConflicting() )
            {
                std::vector<std::pair<std::vector<ConstraintT>, ConstraintT>> bDeds = mpStateTree->variableBounds().getBoundDeductions();
                for( auto bDed = bDeds.begin(); bDed != bDeds.end(); ++bDed )
                {
                    FormulasT subformulas;
                    for( auto cons = bDed->first.begin(); cons != bDed->first.end(); ++cons )
                    {
                        subformulas.emplace_back( carl::FormulaType::NOT, FormulaT( *cons ) ); // @todo store formulas and do not generate a formula here
                    }
                    subformulas.emplace_back( bDed->second );
                    addLemma( FormulaT( carl::FormulaType::OR, std::move( subformulas ) ) );
                }
            }
        }
        mLazyMode = !mFullCheck || Settings::try_first_lazy;
        if( Settings::try_first_lazy && mFullCheck )
        {
            mLazyCheckThreshold = 1;
        }
        else if( !mFullCheck )
        {
            mLazyCheckThreshold = Settings::lazy_check_threshold;
        }
        while( !mRanking.empty() )
        {
			SMTRAT_LOG_DEBUG("smtrat.vs", "Ranking is not empty yet");
            assert( checkRanking() );
//                std::this_thread::sleep_for(std::chrono::milliseconds(1000));
            if( anAnswerFound() )
                return ABORTED;
//            else
//                std::cout << "VSModule iteration" << std::endl;
            #ifdef SMTRAT_DEVOPTION_Statistics
            mStatistics.considerState();
            #endif
            State* currentState = mRanking.begin()->second;
            #ifdef VS_DEBUG
            std::cout << "Ranking:" << std::endl;
            for( auto valDTPair = mRanking.begin(); valDTPair != mRanking.end(); ++valDTPair )
            {
                std::stringstream stream;
                stream << "(" << valDTPair->first.first << ", " << valDTPair->first.second.first << ", " << valDTPair->first.second.second << ")";
                std::cout << std::setw(15) << stream.str();
                std::cout << ":  " << valDTPair->second << std::endl;
            }
            std::cout << "*** Considered state:" << std::endl;
            currentState->printAlone( "*** ", std::cout );
            #endif
            currentState->simplify( mRanking );
            #ifdef VS_DEBUG
            std::cout << "Simplifing results in " << std::endl;
            currentState->printAlone( "*** ", std::cout );
            #endif
//            if( !Settings::split_neq_constraints && !currentState->isInconsistent() && !currentState->takeSubResultCombAgain() )
//            {
//                for( auto cond = currentState->conditions().begin(); cond != currentState->conditions().end(); ++cond )
//                {
//                    if( (*cond)->constraint().hasIntegerValuedVariable() && !(*cond)->constraint().hasRealValuedVariable()
//                        && (*cond)->constraint().relation() == carl::Relation::NEQ )
//                    {
//                        // Split the neq-constraint in a preceeding sat module (make sure that it is there in your strategy when choosing this vssetting)
//                        splitUnequalConstraint( FormulaT( (*cond)->constraint() ) );
//                        assert( currentState->isRoot() );
//                        return UNKNOWN;
//                    }
//                }
//            }
            if( currentState->hasChildrenToInsert() )
            {
				SMTRAT_LOG_DEBUG("smtrat.vs", "Children to insert");
                currentState->rHasChildrenToInsert() = false;
                addStatesToRanking( currentState );
            }
            else
            {
				SMTRAT_LOG_DEBUG("smtrat.vs", "No children to insert");
                if( currentState->isInconsistent() )
                {
					SMTRAT_LOG_DEBUG("smtrat.vs", "Current state is inconsistent");
                    #ifdef VS_LOG_INTERMEDIATE_STEPS
                    logConditions( *currentState, false, "Intermediate_conflict_of_VSModule" );
                    #endif
                    removeStatesFromRanking( *currentState );
                    if( currentState->isRoot() )
                    {
                        updateInfeasibleSubset();
                        return UNSAT;
                    }
                    else
                    {
                        currentState->passConflictToFather( Settings::check_conflict_for_side_conditions );
                        removeStateFromRanking( currentState->rFather() );
                        addStateToRanking( currentState->pFather() );
                    }
                }
                else if( currentState->takeSubResultCombAgain() && currentState->type() == State::COMBINE_SUBRESULTS )
                {
					SMTRAT_LOG_DEBUG("smtrat.vs", "Case 2");
                    #ifdef VS_DEBUG
                    std::cout << "*** Refresh conditons:" << std::endl;
                    #endif
                    if( currentState->refreshConditions( mRanking ) )
                        addStateToRanking( currentState );
                    else
                        addStatesToRanking( currentState );
                    currentState->rTakeSubResultCombAgain() = false;
                    #ifdef VS_DEBUG
                    currentState->printAlone( "   ", std::cout );
                    std::cout << "*** Conditions refreshed." << std::endl;
                    #endif
                }
                else if( currentState->hasRecentlyAddedConditions() )//&& !(currentState->takeSubResultCombAgain() && currentState->isRoot() ) )
                {
					SMTRAT_LOG_DEBUG("smtrat.vs", "Current state has new conditions");
                    #ifdef VS_DEBUG
                    std::cout << "*** Propagate new conditions :" << std::endl;
                    #endif
                    propagateNewConditions(currentState);
                    #ifdef VS_DEBUG
                    std::cout << "*** Propagate new conditions ready." << std::endl;
                    #endif
                }
                else
                {
					SMTRAT_LOG_DEBUG("smtrat.vs", "Case 4");
                    if( Settings::use_variable_bounds && !currentState->checkTestCandidatesForBounds() )
                    {
						SMTRAT_LOG_DEBUG("smtrat.vs", "Test candidates invalidates bounds");
                        currentState->rInconsistent() = true;
                        removeStatesFromRanking( *currentState );
                    }
                    else
                    {
                        if( mLazyMode && currentState->getNumberOfCurrentSubresultCombination() > mLazyCheckThreshold )
                        {
							SMTRAT_LOG_DEBUG("smtrat.vs", "LazyMode case");
                            if( mFullCheck )
                            {
                                if( currentState->cannotBeSolved( true ) )
                                {
                                    removeStatesFromRanking( *mpStateTree );
                                    mLazyMode = false;
                                    mpStateTree->resetCannotBeSolvedLazyFlags();
                                    addStatesToRanking( mpStateTree );
                                    continue;
                                }
                                if( currentState->initIndex( mAllVariables, VariableValuationStrategy::OPTIMIZE_BEST, Settings::prefer_equation_over_all, true, Settings::use_fixed_variable_order ) )
                                {
                                    currentState->initConditionFlags();
                                    currentState->resetConflictSets();
                                    while( !currentState->children().empty() )
                                    {
                                        State* toDelete = currentState->rChildren().back();
                                        removeStatesFromRanking( *toDelete );
                                        currentState->rChildren().pop_back();
                                        currentState->resetInfinityChild( toDelete );
                                        delete toDelete;  // DELETE STATE
                                    }
                                    currentState->updateIntTestCandidates();
                                }
                                else
                                {
                                    removeStatesFromRanking( *currentState );
                                    currentState->rCannotBeSolvedLazy() = true;
                                    addStateToRanking( currentState );
                                }
                            }
                            else
                            {
                                if( currentState->cannotBeSolved( true ) )
                                {
                                    return UNKNOWN;
                                }
                                removeStatesFromRanking( *currentState );
                                currentState->rCannotBeSolvedLazy() = true;
                                addStateToRanking( currentState );
                            }
                        }
                        switch( currentState->type() )
                        {
                            case State::SUBSTITUTION_TO_APPLY:
                            {
								SMTRAT_LOG_DEBUG("smtrat.vs", "Applying substitution");
                                #ifdef VS_DEBUG
                                std::cout << "*** SubstituteAll changes it to:" << std::endl;
                                #else
                                #ifdef VS_MODULE_VERBOSE_INTEGERS
                                bool minf = currentState->substitution().type() == Substitution::MINUS_INFINITY;
                                if( !minf )
                                {
                                    std::cout << std::string( currentState->treeDepth()*3, ' ') << "Test candidate  " << std::endl;
                                    currentState->substitution().print( true, false, std::cout, std::string( currentState->treeDepth()*3, ' '));
                                }
                                #endif
                                #endif
                                if( !substituteAll( currentState, currentState->rFather().rConditions() ) )
                                {
                                    // Delete the currently considered state.
                                    assert( currentState->rInconsistent() );
                                    removeStateFromRanking( *currentState );
                                }
                                #ifndef VS_DEBUG
                                #ifdef VS_MODULE_VERBOSE_INTEGERS
                                if( minf )
                                {
                                    std::cout << std::string( currentState->treeDepth()*3, ' ') << "Test candidate  [from -inf]" << std::endl;
                                    currentState->substitution().print( true, false, std::cout, std::string( currentState->treeDepth()*3, ' '));
                                }
                                #endif
                                #endif
                                #ifdef VS_DEBUG
                                std::cout << "*** SubstituteAll ready." << std::endl;
                                #endif
                                break;
                            }
                            case State::COMBINE_SUBRESULTS:
                            {
								SMTRAT_LOG_DEBUG("smtrat.vs", "Combining subresults");
                                #ifdef VS_DEBUG
                                std::cout << "*** Refresh conditons:" << std::endl;
                                #endif
                                if( currentState->nextSubResultCombination() )
                                {
                                    if( currentState->refreshConditions( mRanking ) )
                                    {
                                        #ifdef SMTRAT_DEVOPTION_Statistics
                                        mStatistics.considerCase();
                                        #endif
                                        addStateToRanking( currentState );
                                    }
                                    else
                                        addStatesToRanking( currentState );
                                    #ifdef VS_DEBUG
                                    currentState->printAlone( "   ", std::cout );
                                    #endif
                                }
                                else
                                {
                                    // If it was the last combination, delete the state.
                                    currentState->rInconsistent() = true;
                                    removeStatesFromRanking( *currentState );
                                    currentState->rFather().rMarkedAsDeleted() = false;
                                    addStateToRanking( currentState->pFather() );

                                }
                                #ifdef VS_DEBUG
                                std::cout << "*** Conditions refreshed." << std::endl;
                                #endif
                                break;
                            }
                            case State::TEST_CANDIDATE_TO_GENERATE:
                            {
								SMTRAT_LOG_DEBUG("smtrat.vs", "Generating test candidate");
                                // Set the index, if not already done, to the best variable to eliminate next.
                                if( currentState->index() == carl::Variable::NO_VARIABLE )
                                    currentState->initIndex( mAllVariables, VariableValuationStrategy::OPTIMIZE_BEST, Settings::prefer_equation_over_all, false, Settings::use_fixed_variable_order );
                                else if( currentState->tryToRefreshIndex() )
                                {
                                    if( currentState->initIndex( mAllVariables, VariableValuationStrategy::OPTIMIZE_BEST, Settings::prefer_equation_over_all, false, Settings::use_fixed_variable_order ) )
                                    {
                                        currentState->initConditionFlags();
                                        currentState->resetConflictSets();
                                        while( !currentState->children().empty() )
                                        {
                                            State* toDelete = currentState->rChildren().back();
                                            removeStatesFromRanking( *toDelete );
                                            currentState->rChildren().pop_back();
                                            currentState->resetInfinityChild( toDelete );
                                            delete toDelete;  // DELETE STATE
                                        }
                                        currentState->updateIntTestCandidates();
                                    }
                                }
                                // Find the most adequate conditions to continue.
                                const vs::Condition* currentCondition;
                                if( !currentState->bestCondition( currentCondition, mAllVariables.size(), Settings::prefer_equation_over_all ) )
                                {
									SMTRAT_LOG_DEBUG("smtrat.vs", "Not the best condition");
                                    if( !(*currentState).cannotBeSolved( mLazyMode ) && currentState->tooHighDegreeConditions().empty() )
                                    {
                                        if( currentState->conditions().empty() )
                                        {
											SMTRAT_LOG_DEBUG("smtrat.vs", "No conditions");
                                            #ifdef VS_DEBUG
                                            std::cout << "*** Check ancestors!" << std::endl;
                                            #endif
                                            // Check if there are still conditions in any ancestor, which have not been considered.
                                            State * unfinishedAncestor;
                                            if( currentState->unfinishedAncestor( unfinishedAncestor ) )
                                            {
												SMTRAT_LOG_DEBUG("smtrat.vs", "Has unfinished ancestor");
                                                // Go back to this ancestor and refine.
                                                removeStatesFromRanking( *unfinishedAncestor );
                                                unfinishedAncestor->extendSubResultCombination();
                                                unfinishedAncestor->rType() = State::COMBINE_SUBRESULTS;
                                                if( unfinishedAncestor->refreshConditions( mRanking ) )
                                                    addStateToRanking( unfinishedAncestor );
                                                else
                                                    addStatesToRanking( unfinishedAncestor );
                                                #ifdef VS_DEBUG
                                                std::cout << "*** Found an unfinished ancestor:" << std::endl;
                                                unfinishedAncestor->printAlone();
                                                #endif
                                            }
                                            else // Solution.
                                            {
												SMTRAT_LOG_DEBUG("smtrat.vs", "Has a solution");
												if( !solutionInDomain() )
                                                {
													bool cannotBeSolved = false;
													State* cur = currentState;
													while (!cannotBeSolved && cur != nullptr) {
														cannotBeSolved = cannotBeSolved || cur->cannotBeSolved(mLazyMode);
														cur = cur->pFather();
													}
													SMTRAT_LOG_DEBUG("smtrat.vs", "Checking for solvability " << mLazyMode << " -> " << currentState->cannotBeSolved(mLazyMode));
													if (!cannotBeSolved) {
														SMTRAT_LOG_DEBUG("smtrat.vs", "Solution is not in domain");
														return UNKNOWN;
													} else {
														SMTRAT_LOG_DEBUG("smtrat.vs", "Found infeasibility of this state");
													}
                                                }
                                                else
                                                {
													SMTRAT_LOG_DEBUG("smtrat.vs", "Checking the consistency");
                                                    return consistencyTrue();
                                                }
                                            }
                                        }
                                        // It is a state, where all conditions have been used for test candidate generation.
                                        else
                                        {
                                            // Check whether there are still test candidates in form of children left.
                                            bool currentStateHasChildrenToConsider = false;
                                            bool currentStateHasChildrenWithToHighDegree = false;
                                            auto child = currentState->rChildren().begin();
                                            while( child != currentState->children().end() )
                                            {
                                                if( !(**child).isInconsistent() )
                                                {
                                                    if( !(**child).markedAsDeleted() )
                                                        addStateToRanking( *child );
                                                    if( !(**child).cannotBeSolved( mLazyMode ) && !(**child).markedAsDeleted() )
                                                        currentStateHasChildrenToConsider = true;
                                                    else
                                                        currentStateHasChildrenWithToHighDegree = true;
                                                }
                                                child++;
                                            }

                                            if( !currentStateHasChildrenToConsider )
                                            {
                                                if( !currentStateHasChildrenWithToHighDegree )
                                                {
                                                    currentState->rInconsistent() = true;
                                                    #ifdef VS_LOG_INTERMEDIATE_STEPS
                                                    logConditions( *currentState, false, "Intermediate_conflict_of_VSModule" );
                                                    #endif
                                                    removeStatesFromRanking( *currentState );
                                                    if( currentState->isRoot() )
                                                        updateInfeasibleSubset();
                                                    else
                                                    {
                                                        currentState->passConflictToFather( Settings::check_conflict_for_side_conditions );
                                                        removeStateFromRanking( currentState->rFather() );
                                                        addStateToRanking( currentState->pFather() );
                                                    }
                                                }
                                                else
                                                {
                                                    currentState->rMarkedAsDeleted() = true;
                                                    removeStateFromRanking( *currentState );
                                                }
                                            }
                                        }
                                    }
                                    else
                                    {
                                        if( (*currentState).cannotBeSolved( mLazyMode ) )
                                        {
                                            // If we need to involve another approach.
                                            Answer result = runBackendSolvers( currentState );
                                            switch( result )
                                            {
                                                case SAT:
                                                {
                                                    currentState->rCannotBeSolved() = true;
                                                    State * unfinishedAncestor;
                                                    if( currentState->unfinishedAncestor( unfinishedAncestor ) )
                                                    {
                                                        // Go back to this ancestor and refine.
                                                        removeStatesFromRanking( *unfinishedAncestor );
                                                        unfinishedAncestor->extendSubResultCombination();
                                                        unfinishedAncestor->rType() = State::COMBINE_SUBRESULTS;
                                                        if( unfinishedAncestor->refreshConditions( mRanking ) )
                                                            addStateToRanking( unfinishedAncestor );
                                                        else
                                                            addStatesToRanking( unfinishedAncestor );
                                                    }
                                                    else // Solution.
                                                    {
                                                        if( !solutionInDomain() )
                                                        {
                                                            return UNKNOWN;
                                                        }
                                                        else
                                                        {
                                                            return consistencyTrue();
                                                        }
                                                    }
                                                    break;
                                                }
                                                case UNSAT:
                                                {
                                                    break;
                                                }
                                                case UNKNOWN:
                                                {
                                                    return UNKNOWN;
                                                }
                                                case ABORTED:
                                                {
                                                    return ABORTED;
                                                }
                                                default:
                                                {
                                                    std::cout << "Error: UNKNOWN answer in method " << __func__ << " line " << __LINE__ << std::endl;
                                                    return UNKNOWN;
                                                }
                                            }
                                        }
                                        else
                                        {
                                            currentState->rCannotBeSolved() = true;
                                            addStateToRanking( currentState );
                                        }
                                    }
                                }
                                // Generate test candidates for the chosen variable and the chosen condition.
                                else
                                {
                                    if( Settings::local_conflict_search && currentState->index().type() == carl::VariableType::VT_REAL && currentState->hasLocalConflict() )
                                    {
                                        removeStatesFromRanking( *currentState );
                                        addStateToRanking( currentState );
                                    }
                                    else
                                    {
                                        #ifdef VS_DEBUG
                                        std::cout << "*** Eliminate " << currentState->index() << " in ";
                                        std::cout << currentCondition->constraint();
                                        std::cout << " creates:" << std::endl;
                                        #endif
                                        eliminate( currentState, currentState->index(), currentCondition );
                                        #ifdef VS_DEBUG
                                        std::cout << "*** Eliminate ready." << std::endl;
                                        #endif
                                    }
                                }
                                break;
                            }
                            default:
								SMTRAT_LOG_DEBUG("smtrat.vs", "Fallthrough case.");
                                assert( false );
                        }
                    }
                }
            }
        }
        if( mpStateTree->markedAsDeleted() )
        {
			SMTRAT_LOG_DEBUG("smtrat.vs", "State tree is to be deleted");
            #ifdef VS_DEBUG
            printAll();
            #endif
            return UNKNOWN;
        }
		SMTRAT_LOG_DEBUG("smtrat.vs", "Nothing was found, return UNSAT");
        #ifdef VS_LOG_INTERMEDIATE_STEPS
        if( mpStateTree->conflictSets().empty() ) logConditions( *mpStateTree, false, "Intermediate_conflict_of_VSModule" );
        #endif
        assert( !mpStateTree->conflictSets().empty() );
        updateInfeasibleSubset();
        #ifdef VS_DEBUG
        printAll();
        #endif
        return UNSAT;
    }

    template<class Settings>
    void VSModule<Settings>::updateModel() const
    {
        clearModel();
        if( solverState() == SAT )
        {
            if( mFormulaConditionMap.empty() )
                return;
            for( size_t i = mVariableVector.size(); i<=mRanking.begin()->second->treeDepth(); ++i )
            {
                std::stringstream outA;
                outA << "m_inf_" << id() << "_" << i;
                carl::Variable minfVar( carl::fresh_real_variable( outA.str() ) );
                std::stringstream outB;
                outB << "eps_" << id() << "_" << i;
                carl::Variable epsVar( carl::fresh_real_variable( outB.str() ) );
                mVariableVector.push_back( std::pair<carl::Variable,carl::Variable>( minfVar, epsVar ) );
            }
            assert( !mRanking.empty() );
            carl::Variables allVarsInRoot;
            mpStateTree->variables( allVarsInRoot );
            RationalAssignment rationalAssignments;
            const State* state = mRanking.begin()->second;
            while( !state->isRoot() )
            {
                const Substitution& sub = state->substitution();
                ModelValue ass;
                if( sub.type() == Substitution::MINUS_INFINITY )
                    ass = SqrtEx( mVariableVector.at( state->treeDepth()-1 ).first );
                else
                {
                    assert( sub.type() != Substitution::PLUS_INFINITY );
                    SqrtEx substitutedTerm = substitute(sub.term(), rationalAssignments );
                    if( sub.type() == Substitution::PLUS_EPSILON )
                    {
                        assert( state->substitution().variable().type() != carl::VariableType::VT_INT );
                        ass = substitutedTerm + SqrtEx( mVariableVector.at( state->treeDepth()-1 ).second );
                    }
                    else
                    {
                        if( substitutedTerm.isRational() )
                            ass = substitutedTerm.asRational();
                        if( substitutedTerm.is_polynomial() )
                            ass = carl::createSubstitution<Rational,Poly,ModelPolynomialSubstitution>( substitutedTerm.as_polynomial() );
                        else
                            ass = substitutedTerm;
                    }
                }
                mModel.insert(std::make_pair(state->substitution().variable(), ass));
                state = state->pFather();
            }
            if( mRanking.begin()->second->cannotBeSolved( mLazyMode ) )
                Module::getBackendsModel();
            // All variables which occur in the root of the constructed state tree but were incidentally eliminated
            // (during the elimination of another variable) can have an arbitrary assignment. If the variable has the
            // real domain, we leave at as a parameter, and, if it has the integer domain we assign 0 to it.
            for( auto var = allVarsInRoot.begin(); var != allVarsInRoot.end(); ++var )
            {
                mModel.insert(std::make_pair(*var, carl::createSubstitution<Rational,Poly,ModelPolynomialSubstitution>( Poly(0) )));
            }
        }
    }

    template<class Settings>
    Answer VSModule<Settings>::consistencyTrue()
    {
        #ifdef VS_LOG_INTERMEDIATE_STEPS
        checkAnswer();
        #endif
        #ifdef VS_PRINT_ANSWERS
        printAnswer();
        #endif
        #ifdef VS_DEBUG
        printAll();
        #endif
        return SAT;
    }

    template<class Settings>
    void VSModule<Settings>::eliminate( State* _currentState, const carl::Variable& _eliminationVar, const vs::Condition* _condition )
    {
        // Get the constraint of this condition.
        const ConstraintT& constraint = (*_condition).constraint();
        assert( _condition->constraint().variables().has( _eliminationVar ) );
        bool generatedTestCandidateBeingASolution = false;
        unsigned numberOfAddedChildren = 0;
        carl::PointerSet<vs::Condition> oConditions;
        oConditions.insert( _condition );
        if( !Settings::use_variable_bounds || _currentState->hasRootsInVariableBounds( _condition, Settings::sturm_sequence_for_root_check ) )
        {
            carl::Relation relation = (*_condition).constraint().relation();
            if( !Settings::use_strict_inequalities_for_test_candidate_generation )
            {
                if( relation == carl::Relation::LESS || relation == carl::Relation::GREATER || relation == carl::Relation::NEQ )
                {
                    _currentState->rTooHighDegreeConditions().insert( _condition );
                    _condition->rFlag() = true;
                    return;
                }
            }
            // Determine the substitution type: normal or +epsilon
            bool weakConstraint = (relation == carl::Relation::EQ || relation == carl::Relation::LEQ || relation == carl::Relation::GEQ);
            Substitution::Type subType = weakConstraint ? Substitution::NORMAL : Substitution::PLUS_EPSILON;
            std::vector< Poly > factors = std::vector< Poly >();
            ConstraintsT sideConditions;
            if( Settings::elimination_with_factorization && !carl::is_trivial(constraint.lhs_factorization()))
            {
                auto& factorization = constraint.lhs_factorization();
                for( auto iter = factorization.begin(); iter != factorization.end(); ++iter )
                {
                    if( carl::variables(iter->first).has( _eliminationVar ) )
                        factors.push_back( iter->first );
                    else
                    {
                        ConstraintT cons = ConstraintT( iter->first, carl::Relation::NEQ );
                        if( cons != ConstraintT( true ) )
                        {
                            assert( cons != ConstraintT( false ) );
                            sideConditions.insert( cons );
                        }
                    }
                }
            }
            else
                factors.push_back( constraint.lhs() );
            for( auto factor = factors.begin(); factor != factors.end(); ++factor )
            {
                #ifdef VS_DEBUG
                std::cout << "Eliminate for " << *factor << std::endl;
                #endif
                auto varInfo = carl::var_info(*factor, _eliminationVar, true);
                const auto& coeffs = varInfo.coeffs();
                assert( !coeffs.empty() );
                // Generate test candidates for the chosen variable considering the chosen constraint.
                switch( coeffs.rbegin()->first )
                {
                    case 0:
                    {
                        assert( false );
                        break;
                    }
                    //degree = 1
                    case 1:
                    {
                        Poly constantCoeff;
                        auto iter = coeffs.find( 0 );
                        if( iter != coeffs.end() ) constantCoeff = iter->second;
                        // Create state ({b!=0} + oldConditions, [x -> -c/b]):
                        ConstraintT cons = ConstraintT( coeffs.rbegin()->second, carl::Relation::NEQ );
                        if( cons == ConstraintT( false ) )
                        {
                            if( relation == carl::Relation::EQ )
                                generatedTestCandidateBeingASolution = sideConditions.empty();
                        }
                        else
                        {
                            ConstraintsT sideCond = sideConditions;
                            if( cons != ConstraintT( true ) )
                                sideCond.insert( cons );
                            SqrtEx sqEx = SqrtEx( -constantCoeff, Poly(0), coeffs.rbegin()->second, Poly(0) );
                            Substitution sub = Substitution( _eliminationVar, sqEx, subType, carl::PointerSet<vs::Condition>(oConditions), std::move(sideCond) );
                            std::vector<State*> addedChildren = _currentState->addChild( sub );
                            if( !addedChildren.empty() )
                            {
                                if( relation == carl::Relation::EQ && !_currentState->children().back()->hasSubstitutionResults() )
                                {
                                    _currentState->rChildren().back()->setOriginalCondition( _condition );
                                    generatedTestCandidateBeingASolution = true;
                                }
                                // Add its valuation to the current ranking.
                                while( !addedChildren.empty() )
                                {
                                    addStatesToRanking( addedChildren.back() );
                                    addedChildren.pop_back();
                                }
                                ++numberOfAddedChildren;
                                #ifdef VS_DEBUG
                                (*(*_currentState).rChildren().back()).print( "   ", std::cout );
                                #endif
                            }
                        }
                        break;
                    }
                    //degree = 2
                    case 2:
                    {
                        Poly constantCoeff;
                        auto iter = coeffs.find( 0 );
                        if( iter != coeffs.end() ) constantCoeff = iter->second;
                        Poly linearCoeff;
                        iter = coeffs.find( 1 );
                        if( iter != coeffs.end() ) linearCoeff = iter->second;
                        Poly radicand = carl::pow(linearCoeff, 2) - Rational( 4 ) * coeffs.rbegin()->second * constantCoeff;
                        bool constraintHasZeros = false;
                        ConstraintT cons11 = ConstraintT( coeffs.rbegin()->second, carl::Relation::EQ );
                        if( cons11 != ConstraintT( false ) )
                        {
                            // Create state ({a==0, b!=0} + oldConditions, [x -> -c/b]):
                            ConstraintT cons12 = ConstraintT( linearCoeff, carl::Relation::NEQ );
                            if( cons12 != ConstraintT( false ) )
                            {
                                ConstraintsT sideCond = sideConditions;
                                if( cons11 != ConstraintT( true ) )
                                    sideCond.insert( cons11 );
                                if( cons12 != ConstraintT( true ) )
                                    sideCond.insert( cons12 );
                                SqrtEx sqEx = SqrtEx( -constantCoeff, Poly(0), linearCoeff, Poly(0) );
                                Substitution sub = Substitution( _eliminationVar, sqEx, subType, carl::PointerSet<vs::Condition>(oConditions), std::move(sideCond) );
                                std::vector<State*> addedChildren = _currentState->addChild( sub );
                                if( !addedChildren.empty() )
                                {
                                    if( relation == carl::Relation::EQ && !_currentState->children().back()->hasSubstitutionResults() )
                                    {
                                        _currentState->rChildren().back()->setOriginalCondition( _condition );
                                        generatedTestCandidateBeingASolution = true;
                                    }
                                    // Add its valuation to the current ranking.
                                    while( !addedChildren.empty() )
                                    {
                                        addStatesToRanking( addedChildren.back() );
                                        addedChildren.pop_back();
                                    }
                                    ++numberOfAddedChildren;
                                    #ifdef VS_DEBUG
                                    (*(*_currentState).rChildren().back()).print( "   ", std::cout );
                                    #endif
                                }
                                constraintHasZeros = true;
                            }
                        }
                        ConstraintT cons21 = ConstraintT( radicand, carl::Relation::GEQ );
                        if( cons21 != ConstraintT( false ) )
                        {
                            ConstraintT cons22 = ConstraintT( coeffs.rbegin()->second, carl::Relation::NEQ );
                            if( cons22 != ConstraintT( false ) )
                            {
                                ConstraintsT sideCond = sideConditions;
                                if( cons21 != ConstraintT( true ) )
                                    sideCond.insert( cons21 );
                                if( cons22 != ConstraintT( true ) )
                                    sideCond.insert( cons22 );
                                // Create state ({a!=0, b^2-4ac>=0} + oldConditions, [x -> (-b-sqrt(b^2-4ac))/2a]):
                                SqrtEx sqExA = SqrtEx( -linearCoeff, Poly(-1), Rational( 2 ) * coeffs.rbegin()->second, radicand );
                                Substitution subA = Substitution( _eliminationVar, sqExA, subType, carl::PointerSet<vs::Condition>(oConditions), ConstraintsT(sideCond) );
                                std::vector<State*> addedChildrenA = _currentState->addChild( subA );
                                if( !addedChildrenA.empty() )
                                {
                                    if( relation == carl::Relation::EQ && !_currentState->children().back()->hasSubstitutionResults() )
                                    {
                                        _currentState->rChildren().back()->setOriginalCondition( _condition );
                                        generatedTestCandidateBeingASolution = true;
                                    }
                                    // Add its valuation to the current ranking.
                                    while( !addedChildrenA.empty() )
                                    {
                                        addStatesToRanking( addedChildrenA.back() );
                                        addedChildrenA.pop_back();
                                    }
                                    ++numberOfAddedChildren;
                                    #ifdef VS_DEBUG
                                    (*(*_currentState).rChildren().back()).print( "   ", std::cout );
                                    #endif
                                }
                                // Create state ({a!=0, b^2-4ac>=0} + oldConditions, [x -> (-b+sqrt(b^2-4ac))/2a]):
                                SqrtEx sqExB = SqrtEx( -linearCoeff, Poly(1), Rational( 2 ) * coeffs.rbegin()->second, radicand );
                                Substitution subB = Substitution( _eliminationVar, sqExB, subType, carl::PointerSet<vs::Condition>(oConditions), std::move(sideCond) );
                                std::vector<State*> addedChildrenB = _currentState->addChild( subB );
                                if( !addedChildrenB.empty() )
                                {
                                    if( relation == carl::Relation::EQ && !_currentState->children().back()->hasSubstitutionResults() )
                                    {
                                        _currentState->rChildren().back()->setOriginalCondition( _condition );
                                        generatedTestCandidateBeingASolution = true;
                                    }
                                    // Add its valuation to the current ranking.
                                    while( !addedChildrenB.empty() )
                                    {
                                        addStatesToRanking( addedChildrenB.back() );
                                        addedChildrenB.pop_back();
                                    }
                                    ++numberOfAddedChildren;
                                    #ifdef VS_DEBUG
                                    (*(*_currentState).rChildren().back()).print( "   ", std::cout );
                                    #endif
                                }
                                constraintHasZeros = true;
                            }
                        }
                        if( !constraintHasZeros && relation == carl::Relation::EQ )
                            generatedTestCandidateBeingASolution = sideConditions.empty();
                        break;
                    }
                    //degree > 2 (> 3)
                    default:
                    {
                        _currentState->rTooHighDegreeConditions().insert( _condition );
                        break;
                    }
                }
            }
        }
        if( !generatedTestCandidateBeingASolution && !_currentState->isInconsistent() )
//        if( _eliminationVar.type() != carl::VariableType::VT_INT && !generatedTestCandidateBeingASolution && !_currentState->isInconsistent() )
        {
            // Create state ( Conditions, [x -> -infinity]):
            Substitution sub = Substitution( _eliminationVar, Substitution::MINUS_INFINITY, carl::PointerSet<vs::Condition>(oConditions) );
            std::vector<State*> addedChildren = _currentState->addChild( sub );
            if( !addedChildren.empty() )
            {
                // Add its valuation to the current ranking.
                while( !addedChildren.empty() )
                {
                    addStatesToRanking( addedChildren.back() );
                    addedChildren.pop_back();
                }
                numberOfAddedChildren++;
                #ifdef VS_DEBUG
                (*(*_currentState).rChildren().back()).print( "   ", std::cout );
                #endif
            }
        }
//        if( _eliminationVar.type() == carl::VariableType::VT_INT )
//        {
//            if( !generatedTestCandidateBeingASolution && !_currentState->isInconsistent() )
//            {
//                // Create state ( Conditions, [x -> -infinity]):
//                Substitution sub = Substitution( _eliminationVar, Substitution::PLUS_INFINITY, carl::PointerSet<vs::Condition>(oConditions) );
//                std::vector<State*> addedChildren = _currentState->addChild( sub );
//                if( !addedChildren.empty() )
//                {
//                    // Add its valuation to the current ranking.
//                    while( !addedChildren.empty() )
//                    {
//                        addStatesToRanking( addedChildren.back() );
//                        addedChildren.pop_back();
//                    }
//                    numberOfAddedChildren++;
//                    #ifdef VS_DEBUG
//                    (*(*_currentState).rChildren().back()).print( "   ", std::cout );
//                    #endif
//                }
//            }
//        }
        if( generatedTestCandidateBeingASolution )
        {
            _currentState->rTooHighDegreeConditions().clear();
            for( auto cond = _currentState->rConditions().begin(); cond != _currentState->conditions().end(); ++cond )
                (**cond).rFlag() = true;
            assert( numberOfAddedChildren <= _currentState->children().size() );
            while( _currentState->children().size() > numberOfAddedChildren )
            {
                State* toDelete = *_currentState->rChildren().begin();
                removeStatesFromRanking( *toDelete );
                _currentState->resetConflictSets();
                _currentState->rChildren().erase( _currentState->rChildren().begin() );
                _currentState->resetInfinityChild( toDelete );
                delete toDelete;  // DELETE STATE
            }
            _currentState->updateIntTestCandidates();
            if( numberOfAddedChildren == 0 )
            {
                ConditionSetSet conflictSet;
                carl::PointerSet<vs::Condition> condSet;
                condSet.insert( _condition );
                conflictSet.insert( condSet );
                _currentState->addConflicts( NULL, std::move(conflictSet) );
                _currentState->rInconsistent() = true;
            }
        }
        else
            (*_condition).rFlag() = true;
        addStateToRanking( _currentState );
    }

    template<class Settings>
    bool VSModule<Settings>::substituteAll( State* _currentState, ConditionList& _conditions )
    {
        /*
         * Create a vector to store the results of each single substitution. Each entry corresponds to
         * the results of a single substitution. These results can be considered as a disjunction of
         * conjunctions of constraints.
         */
        std::vector<DisjunctionOfConditionConjunctions> allSubResults;
        // The substitution to apply.
        assert( !_currentState->isRoot() );
        const Substitution& currentSubs = _currentState->substitution();
        // The variable to substitute.
        const carl::Variable& substitutionVariable = currentSubs.variable();
        // The conditions of the currently considered state, without the one getting just eliminated.
        ConditionList oldConditions;
        bool anySubstitutionFailed = false;
        bool allSubstitutionsApplied = true;
        ConditionSetSet conflictSet;
        EvalDoubleIntervalMap solBox = Settings::use_variable_bounds ? _currentState->father().variableBounds().getIntervalMap() : EvalDoubleIntervalMap();
        // Apply the substitution to the given conditions.
        for( auto cond = _conditions.begin(); cond != _conditions.end(); ++cond )
        {
            // The constraint to substitute in.
            const ConstraintT& currentConstraint = (**cond).constraint();
            // Does the condition contain the variable to substitute.
            //auto var = currentConstraint.variables().find( substitutionVariable );
            if( !currentConstraint.variables().has( substitutionVariable ) )
            {
                if( !anySubstitutionFailed )
                {
                    oldConditions.push_back( new vs::Condition( currentConstraint, mpConditionIdAllocator->get(), (**cond).valuation() ) );
                    oldConditions.back()->pOriginalConditions()->insert( *cond );
                }
            }
            else
            {
                DisjunctionOfConstraintConjunctions subResult;
                carl::Variables conflVars;
                bool substitutionCouldBeApplied = substitute( currentConstraint, currentSubs, subResult, Settings::virtual_substitution_according_paper, conflVars, solBox );
                allSubstitutionsApplied &= substitutionCouldBeApplied;
                // Create the the conditions according to the just created constraint prototypes.
                if( substitutionCouldBeApplied && subResult.empty() )
                {
                    anySubstitutionFailed = true;
                    carl::PointerSet<vs::Condition> condSet;
                    condSet.insert( *cond );
                    if( _currentState->pOriginalCondition() != NULL )
                        condSet.insert( _currentState->pOriginalCondition() );
                    if( Settings::use_variable_bounds )
                    {
                        auto conflictingBounds = _currentState->father().variableBounds().getOriginsOfBounds( conflVars );
                        condSet.insert( conflictingBounds.begin(), conflictingBounds.end() );
                    }
                    conflictSet.insert( condSet );
                }
                else
                {
                    if( allSubstitutionsApplied && !anySubstitutionFailed )
                    {
                        allSubResults.emplace_back();
                        DisjunctionOfConditionConjunctions& currentDisjunction = allSubResults.back();
                        for( auto consConj = subResult.begin(); consConj != subResult.end(); ++consConj )
                        {
                            currentDisjunction.emplace_back();
                            ConditionList& currentConjunction = currentDisjunction.back();
                            for( auto cons = consConj->begin(); cons != consConj->end(); ++cons )
                            {
                                currentConjunction.push_back( new vs::Condition( *cons, mpConditionIdAllocator->get(), _currentState->treeDepth() ) );
                                currentConjunction.back()->pOriginalConditions()->insert( *cond );
                            }
                        }
                    }
                }
            }
        }
        bool cleanResultsOfThisMethod = false;
        if( anySubstitutionFailed )
        {
            _currentState->rFather().addConflicts( _currentState->pSubstitution(), std::move(conflictSet) );
            _currentState->rInconsistent() = true;
            while( !_currentState->rConflictSets().empty() )
            {
                const Substitution* sub = _currentState->rConflictSets().begin()->first;
                _currentState->rConflictSets().erase( _currentState->rConflictSets().begin() );
                if( sub != NULL && sub->type() == Substitution::Type::INVALID )
                {
                    delete sub;
                }
            }
            while( !_currentState->children().empty() )
            {
                State* toDelete = _currentState->rChildren().back();
                removeStatesFromRanking( *toDelete );
                _currentState->rChildren().pop_back();
                _currentState->resetInfinityChild( toDelete );
                delete toDelete;  // DELETE STATE
            }
            _currentState->updateIntTestCandidates();
            while( !_currentState->conditions().empty() )
            {
                const vs::Condition* pCond = _currentState->rConditions().back();
                _currentState->rConditions().pop_back();
                if( Settings::use_variable_bounds )
                    _currentState->rVariableBounds().removeBound( pCond->constraint(), pCond );
                mpConditionIdAllocator->free( pCond->id() );
                delete pCond;
                pCond = NULL;
            }
            cleanResultsOfThisMethod = true;
        }
        else
        {
            if( !_currentState->isInconsistent() )
            {
                if( allSubstitutionsApplied )
                {
                    removeStatesFromRanking( *_currentState );
                    allSubResults.emplace_back();
                    allSubResults.back().push_back( oldConditions );
                    _currentState->addSubstitutionResults( std::move(allSubResults) );
                    #ifdef VS_MODULE_VERBOSE_INTEGERS
                    _currentState->printSubstitutionResults( std::string( _currentState->treeDepth()*3, ' '), std::cout );
                    #endif
                    addStatesToRanking( _currentState );
                }
                else
                {
                    removeStatesFromRanking( _currentState->rFather() );
                    _currentState->resetConflictSets();
                    while( !_currentState->children().empty() )
                    {
                        State* toDelete = _currentState->rChildren().back();
                        _currentState->rChildren().pop_back();
                        _currentState->resetInfinityChild( toDelete );
                        delete toDelete;  // DELETE STATE
                    }
                    _currentState->updateIntTestCandidates();
                    while( !_currentState->conditions().empty() )
                    {
                        const vs::Condition* pCond = _currentState->rConditions().back();
                        _currentState->rConditions().pop_back();
                        if( Settings::use_variable_bounds )
                            _currentState->rVariableBounds().removeBound( pCond->constraint(), pCond );
                        mpConditionIdAllocator->free( pCond->id() );
                        delete pCond;
                        pCond = NULL;
                    }
                    _currentState->rMarkedAsDeleted() = true;
                    _currentState->rFather().rCannotBeSolved() = true;
                    addStatesToRanking( _currentState->pFather() );
                    cleanResultsOfThisMethod = true;
                }
            }
            #ifdef VS_DEBUG
            _currentState->print( "   ", std::cout );
            #endif
        }
        if( cleanResultsOfThisMethod )
        {
            while( !oldConditions.empty() )
            {
                const vs::Condition* rpCond = oldConditions.back();
                oldConditions.pop_back();
                mpConditionIdAllocator->free( rpCond->id() );
                delete rpCond;
                rpCond = NULL;
            }
            while( !allSubResults.empty() )
            {
                while( !allSubResults.back().empty() )
                {
                    while( !allSubResults.back().back().empty() )
                    {
                        const vs::Condition* rpCond = allSubResults.back().back().back();
                        allSubResults.back().back().pop_back();
                        mpConditionIdAllocator->free( rpCond->id() );
                        delete rpCond;
                        rpCond = NULL;
                    }
                    allSubResults.back().pop_back();
                }
                allSubResults.pop_back();
            }
        }
        return !anySubstitutionFailed;
    }

    namespace vsmodulehelper {
        /**
         * @param _var The variable to check the size of its solution set for.
         * @return true, if it is easy to decide whether this constraint has a finite solution set
         *                in the given variable;
         *          false, otherwise.
         */
        bool hasFinitelyManySolutionsIn(const ConstraintT& constr, const carl::Variable& _var) {
            if (constr.variables().has(_var))
                return true;
            if (constr.relation() == carl::Relation::EQ) {
                if (constr.variables().size() == 1)
                    return true;
            }
            return false;
        }
    }

    template<class Settings>
    void VSModule<Settings>::propagateNewConditions( State* _currentState )
    {

        removeStatesFromRanking( *_currentState );
        // Collect the recently added conditions and mark them as not recently added.
        bool deleteExistingTestCandidates = false;
        ConditionList recentlyAddedConditions;
        for( auto cond = _currentState->rConditions().begin(); cond != _currentState->conditions().end(); ++cond )
        {
            if( (**cond).recentlyAdded() )
            {
                (**cond).rRecentlyAdded() = false;
                recentlyAddedConditions.push_back( *cond );
                if( _currentState->pOriginalCondition() == NULL )
                {
                    bool onlyTestCandidateToConsider = false;
                    if( _currentState->index() != carl::Variable::NO_VARIABLE ) // TODO: Maybe only if the degree is not to high
                        onlyTestCandidateToConsider = vsmodulehelper::hasFinitelyManySolutionsIn((**cond).constraint(), _currentState->index() );
                    if( onlyTestCandidateToConsider )
                        deleteExistingTestCandidates = true;
                }
            }
        }
        addStateToRanking( _currentState );
        if( !_currentState->children().empty() )
        {
            if( deleteExistingTestCandidates || _currentState->initIndex( mAllVariables, VariableValuationStrategy::OPTIMIZE_BEST, Settings::prefer_equation_over_all, false, Settings::use_fixed_variable_order ) )
            {
                _currentState->initConditionFlags();
                // If the recently added conditions make another variable being the best to eliminate next delete all children.
                _currentState->resetConflictSets();
                while( !_currentState->children().empty() )
                {
                    State* toDelete = _currentState->rChildren().back();
                    _currentState->rChildren().pop_back();
                    _currentState->resetInfinityChild( toDelete );
                    delete toDelete;  // DELETE STATE
                }
                _currentState->updateIntTestCandidates();
            }
            else
            {
                bool newTestCandidatesGenerated = false;
                if( _currentState->pOriginalCondition() == NULL )
                {
                    /*
                     * Check if there are new conditions in this state, which would have been better choices
                     * to generate test candidates than those conditions of the already generated test
                     * candidates. If so, generate the test candidates of the better conditions.
                     */
                    for( auto cond = recentlyAddedConditions.begin(); cond != recentlyAddedConditions.end(); ++cond )
                    {
                        if( _currentState->index() != carl::Variable::NO_VARIABLE && (**cond).constraint().variables().has( _currentState->index() ) )
                        {
                            bool worseConditionFound = false;
                            auto child = _currentState->rChildren().begin();
                            while( child != _currentState->children().end() )
                            {
                                if( (**child).substitution().type() != Substitution::MINUS_INFINITY || (**child).substitution().type() != Substitution::PLUS_INFINITY)
                                {
                                    auto oCond = (**child).rSubstitution().rOriginalConditions().begin();
                                    while( !worseConditionFound && oCond != (**child).substitution().originalConditions().end() )
                                    {
                                        if( (**cond).valuate( _currentState->index(), mAllVariables.size(), Settings::prefer_equation_over_all ) > (**oCond).valuate( _currentState->index(), mAllVariables.size(), Settings::prefer_equation_over_all ) )
                                        {
                                            newTestCandidatesGenerated = true;
                                            #ifdef VS_DEBUG
                                            std::cout << "*** Eliminate " << _currentState->index() << " in ";
                                            std::cout << (**cond).constraint();
                                            std::cout << " creates:" << std::endl;
                                            #endif
                                            eliminate( _currentState, _currentState->index(), *cond );
                                            #ifdef VS_DEBUG
                                            std::cout << "*** Eliminate ready." << std::endl;
                                            #endif
                                            worseConditionFound = true;
                                            break;
                                        }
                                        ++oCond;
                                    }
                                    if( worseConditionFound )
                                        break;
                                }
                                ++child;
                            }
                        }
                    }
                }
                // Otherwise, add the recently added conditions to each child of the considered state to
                // which a substitution must be or already has been applied.
                for( auto child = _currentState->rChildren().begin(); child != _currentState->children().end(); ++child )
                {
                    if( (**child).type() != State::SUBSTITUTION_TO_APPLY || (**child).isInconsistent() )
                    {
                        // Apply substitution to new conditions and add the result to the substitution result vector.
                        if( !substituteAll( *child, recentlyAddedConditions ) )
                        {
                            // Delete the currently considered state.
                            assert( (*child)->rInconsistent() );
                            assert( (**child).conflictSets().empty() );
                            removeStateFromRanking( **child );
                        }
                        else if( (**child).isInconsistent() && !(**child).subResultsSimplified() && !(**child).conflictSets().empty() )
                        {
                            addStateToRanking( *child );
                        }
                    }
                    else
                    {
                        if( newTestCandidatesGenerated )
                        {
                            if( !(**child).children().empty() )
                            {
                                (**child).rHasChildrenToInsert() = true;
                            }
                        }
                        else
                        {
                            addStatesToRanking( *child );
                        }
                    }
                }
            }
        }
        _currentState->rHasRecentlyAddedConditions() = false;
    }

    template<class Settings>
    void VSModule<Settings>::addStateToRanking( State* _state )
    {
        if( !_state->markedAsDeleted()
            && !(_state->isInconsistent() && _state->conflictSets().empty() && _state->conditionsSimplified()))
        {
            if( _state->id() != 0 )
            {
                size_t id = _state->id();
                removeStateFromRanking( *_state );
                _state->rID()= id;
            }
            else
            {
                increaseIDCounter();
                _state->rID() = mIDCounter;
            }
            _state->updateValuation( mLazyMode );
            UnsignedTriple key = UnsignedTriple( _state->valuation(), std::pair< size_t, size_t> ( _state->id(), _state->backendCallValuation() ) );
            if( (mRanking.insert( ValStatePair( key, _state ) )).second == false )
            {
                std::cout << "Warning: Could not insert. Entry already exists.";
                std::cout << std::endl;
            }
        }
    }

    template<class Settings>
    void VSModule<Settings>::addStatesToRanking( State* _state )
    {
        addStateToRanking( _state );
        if( _state->conditionsSimplified() && _state->subResultsSimplified() && !_state->takeSubResultCombAgain() && !_state->hasRecentlyAddedConditions() )
            for( auto dt = (*_state).rChildren().begin(); dt != (*_state).children().end(); ++dt )
                addStatesToRanking( *dt );
    }

    template<class Settings>
    void VSModule<Settings>::insertTooHighDegreeStatesInRanking( State* _state )
    {
        if( _state->cannotBeSolved( mLazyMode ) )
            addStateToRanking( _state );
        else
            for( auto dt = (*_state).rChildren().begin(); dt != (*_state).children().end(); ++dt )
                insertTooHighDegreeStatesInRanking( *dt );
    }

    template<class Settings>
    bool VSModule<Settings>::removeStateFromRanking( State& _state )
    {
        UnsignedTriple key = UnsignedTriple( _state.valuation(), std::pair< unsigned, unsigned> ( _state.id(), _state.backendCallValuation() ) );
        auto valDTPair = mRanking.find( key );
        if( valDTPair != mRanking.end() )
        {
            mRanking.erase( valDTPair );
            _state.rID() = 0;
            return true;
        }
        else
            return false;
    }

    template<class Settings>
    void VSModule<Settings>::removeStatesFromRanking( State& _state )
    {
        removeStateFromRanking( _state );
        for( auto dt = _state.rChildren().begin(); dt != _state.children().end(); ++dt )
            removeStatesFromRanking( **dt );
    }

    template<class Settings>
    bool VSModule<Settings>::checkRanking() const
    {
        for( auto valDTPair = mRanking.begin(); valDTPair != mRanking.end(); ++valDTPair )
        {
            if( !mpStateTree->containsState( valDTPair->second ) )
                return false;
        }
        return true;
    }

    template<class Settings>
    FormulaSetT VSModule<Settings>::getReasons( const carl::PointerSet<vs::Condition>& _conditions ) const
    {
        FormulaSetT result;
        if( _conditions.empty() ) return result;
        // Get the original conditions of the root of the root state leading to the given set of conditions.
        carl::PointerSet<vs::Condition> conds = _conditions;
        carl::PointerSet<vs::Condition> oConds;
        while( !(*conds.begin())->originalConditions().empty() )
        {
            for( auto cond = conds.begin(); cond != conds.end(); ++cond )
            {
                assert( !(*cond)->originalConditions().empty() );
                oConds.insert( (*cond)->originalConditions().begin(), (*cond)->originalConditions().end() );
            }
            conds.clear();
            conds.swap( oConds );
        }
        // Get the sub-formulas in the received formula corresponding to these original conditions.
        for( auto oCond = conds.begin(); oCond != conds.end(); ++oCond )
        {
            assert( (*oCond)->originalConditions().empty() );
            auto receivedConstraint = rReceivedFormula().begin();
            while( receivedConstraint != rReceivedFormula().end() )
            {
                if( receivedConstraint->formula().type() == carl::FormulaType::CONSTRAINT )
                {
                    if( (**oCond).constraint() == receivedConstraint->formula().constraint() )
                        break;
                }
                else if( receivedConstraint->formula().type() == carl::FormulaType::NOT && receivedConstraint->formula().subformula().type() == carl::FormulaType::CONSTRAINT )
                {
                    ConstraintT recConstraint = receivedConstraint->formula().subformula().constraint();
                    if( (**oCond).constraint() == ConstraintT( recConstraint.lhs(), carl::inverse( recConstraint.relation() ) ) )
                        break;
                }
                ++receivedConstraint;
            }
            assert( receivedConstraint != rReceivedFormula().end() );
            result.insert( receivedConstraint->formula() );
        }
        return result;
    }

    template<class Settings>
    std::vector<FormulaT> VSModule<Settings>::getReasonsAsVector( const carl::PointerSet<vs::Condition>& _conditions ) const
    {
        std::vector<FormulaT> result;
        if( _conditions.empty() ) return result;
        // Get the original conditions of the root of the root state leading to the given set of conditions.
        carl::PointerSet<vs::Condition> conds = _conditions;
        carl::PointerSet<vs::Condition> oConds;
        while( !(*conds.begin())->originalConditions().empty() )
        {
            for( auto cond = conds.begin(); cond != conds.end(); ++cond )
            {
                assert( !(*cond)->originalConditions().empty() );
                oConds.insert( (*cond)->originalConditions().begin(), (*cond)->originalConditions().end() );
            }
            conds.clear();
            conds.swap( oConds );
        }
        // Get the sub-formulas in the received formula corresponding to these original conditions.
        for( auto oCond = conds.begin(); oCond != conds.end(); ++oCond )
        {
            assert( (*oCond)->originalConditions().empty() );
            auto receivedConstraint = rReceivedFormula().begin();
            while( receivedConstraint != rReceivedFormula().end() )
            {
                if( receivedConstraint->formula().type() == carl::FormulaType::CONSTRAINT )
                {
                    if( (**oCond).constraint() == receivedConstraint->formula().constraint() )
                        break;
                }
                else if( receivedConstraint->formula().type() == carl::FormulaType::NOT && receivedConstraint->formula().subformula().type() == carl::FormulaType::CONSTRAINT )
                {
                    ConstraintT recConstraint = receivedConstraint->formula().subformula().constraint();
                    if( (**oCond).constraint() == ConstraintT( recConstraint.lhs(), carl::inverse( recConstraint.relation() ) ) )
                        break;
                }
                ++receivedConstraint;
            }
            assert( receivedConstraint != rReceivedFormula().end() );
            result.push_back( receivedConstraint->formula() );
        }
        return result;
    }

    template<class Settings>
    void VSModule<Settings>::updateInfeasibleSubset( bool _includeInconsistentTestCandidates )
    {
        if( !Settings::infeasible_subset_generation )
        {
            // Set the infeasible subset to the set of all received constraints.
            mInfeasibleSubsets.emplace_back();
            for( auto cons = rReceivedFormula().begin(); cons != rReceivedFormula().end(); ++cons )
                mInfeasibleSubsets.back().insert( cons->formula() );
            #ifdef SMTRAT_DEVOPTION_Statistics
            mStatistics.addConflict( rReceivedFormula(), mInfeasibleSubsets );
            #endif
            return;
        }
        // Determine the minimum covering sets of the conflict sets, i.e. the infeasible subsets of the root.
        ConditionSetSet minCoverSets;
        ConditionSetSetSet confSets;
        State::ConflictSets::iterator nullConfSet = mpStateTree->rConflictSets().find( NULL );
        if( nullConfSet != mpStateTree->rConflictSets().end() && !_includeInconsistentTestCandidates )
            confSets.insert( nullConfSet->second.begin(), nullConfSet->second.end() );
        else
            for( auto confSet = mpStateTree->rConflictSets().begin(); confSet != mpStateTree->rConflictSets().end(); ++confSet )
                confSets.insert( confSet->second.begin(), confSet->second.end() );
        allMinimumCoveringSets( confSets, minCoverSets );
        assert( !minCoverSets.empty() );
        // Change the globally stored infeasible subset to the smaller one.
        mInfeasibleSubsets.clear();
        for( auto minCoverSet = minCoverSets.begin(); minCoverSet != minCoverSets.end(); ++minCoverSet )
        {
            assert( !minCoverSet->empty() );
            mInfeasibleSubsets.push_back( getReasons( *minCoverSet ) );
            // TODO: Avoid adding multiple identical infeasible subsets.
            // The following input triggers the creation of seven identical infeasible subsets.
            // (x <= 0) and !(x < 0) and !(x = 0)
            break;
        }
        assert( !mInfeasibleSubsets.empty() );
        assert( !mInfeasibleSubsets.back().empty() );
        #ifdef SMTRAT_DEVOPTION_Statistics
        mStatistics.addConflict( rReceivedFormula(), mInfeasibleSubsets );
        #endif
    }

    template<class Settings>
    bool VSModule<Settings>::solutionInDomain()
    {
        bool trySplitting = Settings::use_branch_and_bound && (!Settings::only_split_in_final_call || mFinalCheck);
		SMTRAT_LOG_DEBUG("smtrat.vs", "Try splitting? " << trySplitting << " (from " << Settings::use_branch_and_bound << " " << Settings::only_split_in_final_call << " " << mFinalCheck << ")");
        if( rReceivedFormula().isRealConstraintLiteralConjunction() ) {
			SMTRAT_LOG_DEBUG("smtrat.vs", "Everything is real anyway");
            return true;
		}
        assert( solverState() != UNSAT );
        if( !mRanking.empty() )
        {
			SMTRAT_LOG_DEBUG("smtrat.vs", "Ranking is not empty");
            std::vector<carl::Variable> varOrder;
            State* currentState = mRanking.begin()->second;
            RationalAssignment varSolutions;
            if( currentState->cannotBeSolved( mLazyMode ) )
            {
                Model bmodel = backendsModel();
                for( auto& ass : bmodel )
                {
                    if( ass.second.isSqrtEx() )
                    {
                        assert( ass.second.asSqrtEx().is_constant() && carl::is_integer( ass.second.asSqrtEx().constant_part().constant_part() ) );
                        varSolutions[ass.first.asVariable()] = ass.second.asSqrtEx().constant_part().constant_part();
                    }
                    else if( ass.second.isRAN() )
                    {
                        assert( ass.second.asRAN().is_numeric() && carl::is_integer( ass.second.asRAN().value() ) );
                        varSolutions[ass.first.asVariable()] = ass.second.asRAN().value();
                    }
                }
            }
            while( !currentState->isRoot() )
            {
				SMTRAT_LOG_DEBUG("smtrat.vs", "State is not the root");
                const carl::Variables& tVars = currentState->substitution().termVariables();
                if( currentState->substitution().variable().type() == carl::VariableType::VT_INT )
                {
					SMTRAT_LOG_DEBUG("smtrat.vs", "This variable is integer");
                    for( carl::Variable::Arg v : tVars )
                        varSolutions.insert( std::make_pair( v, Rational(0) ) );
//                    assert( currentState->substitution().type() != Substitution::MINUS_INFINITY );
//                    assert( currentState->substitution().type() != Substitution::PLUS_INFINITY );
                    if( currentState->substitution().type() == Substitution::MINUS_INFINITY || currentState->substitution().type() == Substitution::PLUS_INFINITY )
                    {
						SMTRAT_LOG_DEBUG("smtrat.vs", "substitution is infty");
                        Rational nextIntTCinRange;
                        if( currentState->getNextIntTestCandidate( nextIntTCinRange, Settings::int_max_range ) )
                        {
							SMTRAT_LOG_DEBUG("smtrat.vs", "Get next int test candidate");
                            if( trySplitting )
                            {
								SMTRAT_LOG_DEBUG("smtrat.vs", "Try splitting");
                                #ifdef SMTRAT_DEVOPTION_Statistics
                                mStatistics.branch();
                                #endif
                                branchAt( currentState->substitution().variable(), nextIntTCinRange, std::move(getReasonsAsVector( currentState->substitution().originalConditions() )) );
                            }
                        }
                        else
                        {
							SMTRAT_LOG_DEBUG("smtrat.vs", "Some else case");
                            removeStatesFromRanking( *currentState );
                            currentState->rCannotBeSolved() = true;
                            addStateToRanking( currentState );
                        }
                        return false;
                    }
                    else
                    {
						SMTRAT_LOG_DEBUG("smtrat.vs", "substitution is not infty");
                        assert( currentState->substitution().type() != Substitution::PLUS_EPSILON );
                        if( trySplitting && Settings::branch_and_bound_at_origin )
                        {
							SMTRAT_LOG_DEBUG("smtrat.vs", "Try splitting for B&B");
                            RationalAssignment partialVarSolutions;
                            const Poly& substitutionPoly = (*currentState->substitution().originalConditions().begin())->constraint().lhs();
                            for( auto var = varOrder.rbegin(); var != varOrder.rend(); ++var )
                            {
                                assert( varSolutions.find( *var ) != varSolutions.end() );
                                partialVarSolutions[*var] = varSolutions[*var];
                                Poly subPolyPartiallySubstituted = carl::substitute(substitutionPoly, partialVarSolutions );
                                if( !carl::is_zero(subPolyPartiallySubstituted) )
                                {
                                    Rational cp = subPolyPartiallySubstituted.coprime_factor_without_constant();
                                    assert( carl::get_num( cp ) == Rational(1) || carl::get_num( cp ) == Rational(-1) );
                                    Rational g = carl::get_denom( cp );
                                    if( g > Rational(0) && carl::mod( carl::to_int<Integer>( subPolyPartiallySubstituted.constant_part() ), carl::to_int<Integer>( g ) ) != 0 )
                                    {
                                        Poly branchEx = (subPolyPartiallySubstituted - subPolyPartiallySubstituted.constant_part()) * cp;
                                        Rational branchValue = subPolyPartiallySubstituted.constant_part() * cp;
                                        if( branchAt( branchEx, true, branchValue, std::move(getReasonsAsVector( currentState->substitution().originalConditions() )) ) )
                                        {
                                            #ifdef SMTRAT_DEVOPTION_Statistics
                                            mStatistics.branch();
                                            #endif
                                            return false;
                                        }
                                    }
                                }
                            }
                        }
                        // Insert the (integer!) assignments of the other variables.
                        const SqrtEx& subTerm = currentState->substitution().term();
                        if( carl::is_zero(carl::substitute(subTerm.denominator(), varSolutions )) )
                        {
							SMTRAT_LOG_DEBUG("smtrat.vs", "Something is zero");
                            if( mFinalCheck )
                                splitUnequalConstraint( FormulaT( subTerm.denominator(), carl::Relation::NEQ ) );
                            return false;
                        }
                        auto result = evaluate( subTerm, varSolutions, -1 );
                        Rational evaluatedSubTerm = result.first;
                        bool assIsInteger = result.second;
                        assIsInteger &= carl::is_integer( evaluatedSubTerm );
                        if( !assIsInteger )
                        {
							SMTRAT_LOG_DEBUG("smtrat.vs", "Assignment is not integer");
                            if( trySplitting )
                            {
								SMTRAT_LOG_DEBUG("smtrat.vs", "Try to split");
                                #ifdef SMTRAT_DEVOPTION_Statistics
                                mStatistics.branch();
                                #endif
                                branchAt( currentState->substitution().variable(), evaluatedSubTerm, std::move(getReasonsAsVector( currentState->substitution().originalConditions() )) );
                            }
                            return false;
                        }
                        assert( varSolutions.find( currentState->substitution().variable() ) == varSolutions.end() );
                        varSolutions.insert( std::make_pair( currentState->substitution().variable(), evaluatedSubTerm ) );
                    }
                }
                varOrder.push_back( currentState->substitution().variable() );
                currentState = currentState->pFather();
            }
        }
        return true;
    }

    template<class Settings>
    void VSModule<Settings>::allMinimumCoveringSets( const ConditionSetSetSet& _conflictSets, ConditionSetSet& _minCovSets )
    {
        if( !_conflictSets.empty() )
        {
            // First we construct all possible combinations of combining all single sets of each set of sets.
            // Store for each set an iterator.
            std::vector<ConditionSetSet::iterator> conditionSetSetIters = std::vector<ConditionSetSet::iterator>();
            for( auto conflictSet = _conflictSets.begin(); conflictSet != _conflictSets.end(); ++conflictSet )
            {
                conditionSetSetIters.push_back( (*conflictSet).begin() );
                // Assure, that the set is not empty.
                assert( conditionSetSetIters.back() != (*conflictSet).end() );
            }
            ConditionSetSetSet::iterator conflictSet;
            std::vector<ConditionSetSet::iterator>::iterator conditionSet;
            // Find all covering sets by forming the union of all combinations.
            bool lastCombinationReached = false;
            while( !lastCombinationReached )
            {
                // Create a new combination of vectors.
                carl::PointerSet<vs::Condition> coveringSet;
                bool previousIteratorIncreased = false;
                // For each set of sets in the vector of sets of sets, choose a set in it. We combine
                // these sets by forming their union and store it as a covering set.
                conditionSet = conditionSetSetIters.begin();
                conflictSet  = _conflictSets.begin();
                while( conditionSet != conditionSetSetIters.end() )
                {
                    if( (*conflictSet).empty() )
                    {
                        conflictSet++;
                        conditionSet++;
                    }
                    else
                    {
                        coveringSet.insert( (**conditionSet).begin(), (**conditionSet).end() );
                        // Set the iterator.
                        if( !previousIteratorIncreased )
                        {
                            (*conditionSet)++;
                            if( *conditionSet != (*conflictSet).end() )
                                previousIteratorIncreased = true;
                            else
                                *conditionSet = (*conflictSet).begin();
                        }
                        conflictSet++;
                        conditionSet++;
                        if( !previousIteratorIncreased && conditionSet == conditionSetSetIters.end() )
                            lastCombinationReached = true;
                    }
                }
                _minCovSets.insert( coveringSet );
            }
            /*
             * Delete all covering sets, which are not minimal. We benefit of the set of sets property,
             * which sorts its sets according to the elements they contain. If a set M is a subset of
             * another set M', the position of M in the set of sets is before M'.
             */
            auto minCoverSet = _minCovSets.begin();
            auto coverSet    = _minCovSets.begin();
            coverSet++;
            while( coverSet != _minCovSets.end() )
            {
                auto cond1 = (*minCoverSet).begin();
                auto cond2 = (*coverSet).begin();
                while( cond1 != (*minCoverSet).end() && cond2 != (*coverSet).end() )
                {
                    if( *cond1 != *cond2 )
                        break;
                    cond1++;
                    cond2++;
                }
                if( cond1 == (*minCoverSet).end() )
                    _minCovSets.erase( coverSet++ );
                else
                {
                    minCoverSet = coverSet;
                    coverSet++;
                }
            }
        }
    }

    template<class Settings>
    bool VSModule<Settings>::adaptPassedFormula( const State& _state, FormulaConditionMap& _formulaCondMap )
    {
        if( _state.conditions().empty() ) return false;
        bool changedPassedFormula = false;
        // Collect the constraints to check.
        std::map<ConstraintT,const vs::Condition*> constraintsToCheck;
        for( auto cond = _state.conditions().begin(); cond != _state.conditions().end(); ++cond )
        {
            // Optimization: If the zeros of the polynomial in a weak inequality have already been checked pass the strict version.
            if( Settings::make_constraints_strict_for_backend && _state.allTestCandidatesInvalidated( *cond ) )
            {
                const ConstraintT& constraint = (*cond)->constraint();
                switch( constraint.relation() )
                {
                    case carl::Relation::GEQ:
                    {
                        ConstraintT strictVersion = ConstraintT( constraint.lhs(), carl::Relation::GREATER );
                        constraintsToCheck.insert( std::pair< ConstraintT, const vs::Condition*>( strictVersion, *cond ) );
                        break;
                    }
                    case carl::Relation::LEQ:
                    {
                        ConstraintT strictVersion = ConstraintT( constraint.lhs(), carl::Relation::LESS );
                        constraintsToCheck.insert( std::pair< ConstraintT, const vs::Condition*>( strictVersion, *cond ) );
                        break;
                    }
                    default:
                    {
                        constraintsToCheck.insert( std::pair< ConstraintT, const vs::Condition*>( constraint, *cond ) );
                    }
                }
            }
            else
                constraintsToCheck.insert( std::pair< ConstraintT, const vs::Condition*>( (*cond)->constraint(), *cond ) );
        }
        /*
         * Remove the constraints from the constraints to check, which are already in the passed formula
         * and remove the sub formulas (constraints) in the passed formula, which do not occur in the
         * constraints to add.
         */
        auto subformula = passedFormulaBegin();
        while( subformula != rPassedFormula().end() )
        {
            auto iter = constraintsToCheck.find( subformula->formula().constraint() );
            if( iter != constraintsToCheck.end() )
            {
                _formulaCondMap[subformula->formula()] = iter->second;
                constraintsToCheck.erase( iter );
                ++subformula;
            }
            else
            {
                subformula = eraseSubformulaFromPassedFormula( subformula );
                changedPassedFormula = true;
            }
        }
        // Add the the remaining constraints to add to the passed formula.
        for( auto iter = constraintsToCheck.begin(); iter != constraintsToCheck.end(); ++iter )
        {
            changedPassedFormula = true;
            // @todo store formula and do not generate a new formula every time
            FormulaT formula = FormulaT( iter->first );
            _formulaCondMap[formula] = iter->second;
            addConstraintToInform( formula );
            addSubformulaToPassedFormula( formula );
        }
        return changedPassedFormula;
    }

    template<class Settings>
    Answer VSModule<Settings>::runBackendSolvers( State* _state )
    {
        // Run the backends on the constraint of the state.
        FormulaConditionMap formulaToConditions;
        adaptPassedFormula( *_state, formulaToConditions );
        Answer result = runBackends();
        #ifdef VS_DEBUG
        std::cout << "Ask backend      : ";
        printPassedFormula();
        std::cout << std::endl;
        std::cout << "Answer           : " << result << std::endl;
        #endif
        switch( result )
        {
            case SAT:
            {
                return SAT;
            }
            case UNSAT:
            {
                /*
                * Get the conflict sets formed by the infeasible subsets in the backend.
                */
                ConditionSetSet conflictSet;
                std::vector<Module*>::const_iterator backend = usedBackends().begin();
                while( backend != usedBackends().end() )
                {
                    if( !(*backend)->infeasibleSubsets().empty() )
                    {
                        for( auto infsubset = (*backend)->infeasibleSubsets().begin(); infsubset != (*backend)->infeasibleSubsets().end(); ++infsubset )
                        {
                            carl::PointerSet<vs::Condition> conflict;
                            #ifdef VS_DEBUG
                            std::cout << "Infeasible Subset: {";
                            #endif
                            for( auto subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                            {
                                #ifdef VS_DEBUG
                                std::cout << "  " << *subformula;
                                #endif
                                auto fcPair = formulaToConditions.find( *subformula );
                                assert( fcPair != formulaToConditions.end() );
                                conflict.insert( fcPair->second );
                            }
                            #ifdef VS_DEBUG
                            std::cout << "  }" << std::endl;
                            #endif
                            #ifdef SMTRAT_DEVOPTION_Validation
                            smtrat::ConstraintsT constraints;
                            for( auto cond = conflict.begin(); cond != conflict.end(); ++cond )
                                constraints.insert( (**cond).constraint() );
                            SMTRAT_VALIDATION_ADD("smtrat.modules.vs",(*backend)->moduleName() + "_infeasible_subset",constraints,false);
                            #endif
                            assert( conflict.size() == infsubset->size() );
                            assert( !conflict.empty() );
                            conflictSet.insert( conflict );
                        }
                        break;
                    }
                }
                assert( !conflictSet.empty() );
                _state->addConflictSet( NULL, std::move(conflictSet) );
                removeStatesFromRanking( *_state );

                #ifdef VS_LOG_INTERMEDIATE_STEPS
                logConditions( *_state, false, "Intermediate_conflict_of_VSModule" );
                #endif
                // If the considered state is the root, update the found infeasible subset as infeasible subset.
                if( _state->isRoot() )
                    updateInfeasibleSubset();
                // If the considered state is not the root, pass the infeasible subset to the father.
                else
                {
                    removeStatesFromRanking( *_state );
                    _state->passConflictToFather( Settings::check_conflict_for_side_conditions );
                    removeStateFromRanking( _state->rFather() );
                    addStateToRanking( _state->pFather() );
                }
                return UNSAT;
            }
            case UNKNOWN:
            {
                return UNKNOWN;
            }
            case ABORTED:
            {
                return ABORTED;
            }
            default:
            {
                std::cerr << "UNKNOWN answer type!" << std::endl;
                assert( false );
                return UNKNOWN;
            }
        }
    }

    /**
     * Checks the correctness of the symbolic assignment given by the path from the root
     * state to the satisfying state.
     */
    template<class Settings>
    void VSModule<Settings>::checkAnswer() const
    {
        if( !mRanking.empty() )
        {
            const State* currentState = mRanking.begin()->second;
            while( !(*currentState).isRoot() )
            {
                logConditions( *currentState, true, "Intermediate_result_of_VSModule" );
                currentState = currentState->pFather();
            }
        }
    }

    template<class Settings>
    void VSModule<Settings>::logConditions( const State& _state, bool _assumption, const std::string& _description, bool _logAsDeduction ) const
    {
        if( !_state.conditions().empty() )
        {
            smtrat::ConstraintsT constraints;
            for( auto cond = _state.conditions().begin(); cond != _state.conditions().end(); ++cond )
                constraints.insert( (**cond).constraint() );
            if( _logAsDeduction ) {
                SMTRAT_VALIDATION_ADD("smtrat.modules.vs",_description,constraints,_assumption);
            }
            else
            {
				std::cout << "(assert (and";
                for( auto constraint = constraints.begin(); constraint != constraints.end(); ++constraint )
                    std::cout << " " << *constraint;
                std::cout << " " << _description;
                std::cout << "))" << std::endl;
            }
        }
    }

    #ifdef VS_DEBUG_METHODS

    template<class Settings>
    void VSModule<Settings>::printAll( const std::string& _init, std::ostream& _out ) const
    {
        _out << _init << " Current solver status, where the constraints" << std::endl;
        printFormulaConditionMap( _init, _out );
        _out << _init << " have been added:" << std::endl;
        _out << _init << " mInconsistentConstraintAdded: " << mInconsistentConstraintAdded << std::endl;
        _out << _init << " mIDCounter: " << mIDCounter << std::endl;
        _out << _init << " Current ranking:" << std::endl;
        printRanking( _init, std::cout );
        _out << _init << " State tree:" << std::endl;
        mpStateTree->print( _init + "   ", _out );
    }

    template<class Settings>
    void VSModule<Settings>::printFormulaConditionMap( const std::string& _init, std::ostream& _out ) const
    {
        for( auto cond = mFormulaConditionMap.begin(); cond != mFormulaConditionMap.end(); ++cond )
        {
            _out << _init << "    ";
            _out << cond->first;
            _out << " <-> ";
            cond->second->print( _out );
            _out << std::endl;
        }
    }

    template<class Settings>
    void VSModule<Settings>::printRanking( const std::string& _init, std::ostream& _out ) const
    {
        for( auto valDTPair = mRanking.begin(); valDTPair != mRanking.end(); ++valDTPair )
            (*(*valDTPair).second).printAlone( _init + "   ", _out );
    }

    template<class Settings>
    void VSModule<Settings>::printAnswer( const std::string& _init, std::ostream& _out ) const
    {
        _out << _init << " Answer:" << std::endl;
        if( mRanking.empty() )
            _out << _init << "        UNSAT." << std::endl;
        else
        {
            _out << _init << "        SAT:" << std::endl;
            const State* currentState = mRanking.begin()->second;
            while( !(*currentState).isRoot() )
            {
                _out << _init << "           " << (*currentState).substitution() << std::endl;
                currentState = (*currentState).pFather();
            }
        }
        _out << std::endl;
    }
    #endif
}    // end namespace smtrat


