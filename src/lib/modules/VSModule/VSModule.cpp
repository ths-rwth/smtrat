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
 * File:   VSModule.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * Created on January 18, 2012, 3:45 PM
 */

#include "VSModule.h"
#include <set>

using namespace std;
using namespace GiNaC;
using namespace vs;


namespace smtrat
{
    /**
     * Constructors:
     */
    VSModule::VSModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* _settings, Manager* const _tsManager ):
        Module( _type, _formula, _tsManager ),
        mConditionsChanged( false ),
        mInconsistentConstraintAdded( false ),
        mIDCounter( 0 ),
        #ifdef VS_STATISTICS
        mStepCounter( 0 ),
        #endif
        mpStateTree( new State() ),
        mAllVariables(),
        mFormulaConditionMap(),
        mRanking()
    {}

    /**
     * Destructor:
     */
    VSModule::~VSModule()
    {
        while( !mFormulaConditionMap.empty() )
        {
            vs::Condition* pRecCond = mFormulaConditionMap.begin()->second;
            mFormulaConditionMap.erase( mFormulaConditionMap.begin() );
            delete pRecCond;
        }
        delete mpStateTree;
    }

    /**
     * Adds a constraint to the so far received constraints.
     *
     * @param _subformula The position of the constraint within the received constraints.
     * @return False, if a conflict is detected;
     *         True,  otherwise.
     */
    bool VSModule::assertSubformula( Formula::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula );
        if( (*_subformula)->getType() == REALCONSTRAINT )
        {
            const Constraint* constraint = (*_subformula)->pConstraint();
            vs::Condition*    condition  = new vs::Condition( constraint );
            mFormulaConditionMap[*_subformula] = condition;

            /*
            * Clear the ranking.
            */
            switch( constraint->isConsistent() )
            {
                case 0:
                {
                    eraseDTsOfRanking( *mpStateTree );
                    mIDCounter = 0;
                    mInfeasibleSubsets.clear();
                    mInfeasibleSubsets.push_back( set<const Formula*>() );
                    mInfeasibleSubsets.back().insert( *_subformula );
                    mInconsistentConstraintAdded = true;
                    mSolverState = False;
                    return false;
                }
                case 1:
                {
                    return true;
                }
                case 2:
                {
                    eraseDTsOfRanking( *mpStateTree );
                    mIDCounter = 0;
                    symtab::const_iterator var = constraint->variables().begin();
                    while( var != constraint->variables().end() )
                    {
                        mAllVariables.insert( pair<const string, symbol>( var->first, ex_to<symbol>( var->second ) ) );
                        var++;
                    }
                    ConditionSet oConds = ConditionSet();
                    oConds.insert( condition );

                    vector<DisjunctionOfConditionConjunctions> subResults = vector<DisjunctionOfConditionConjunctions>();
                    DisjunctionOfConditionConjunctions subResult = DisjunctionOfConditionConjunctions();
                    ConditionVector condVector                   = ConditionVector();
                    condVector.push_back( new vs::Condition( constraint, false, oConds, 0 ) );
                    subResult.push_back( condVector );
                    subResults.push_back( subResult );
                    mpStateTree->addSubstitutionResults( subResults );

                    insertDTinRanking( mpStateTree );
                    mConditionsChanged = true;
                    return true;
                }
                default:
                {
                    assert( false );
                    return true;
                }
            }
        }
        return true;
    }

    /**
     * Removes a constraint of the so far received constraints.
     *
     * @param _subformula The position of the constraint within the received constraints.
     */
    void VSModule::removeSubformula( Formula::const_iterator _subformula )
    {
        if( (*_subformula)->getType() == REALCONSTRAINT )
        {
            mInconsistentConstraintAdded = false;
            auto formulaConditionPair = mFormulaConditionMap.find( *_subformula );
            assert( formulaConditionPair != mFormulaConditionMap.end() );
            vs::Condition* condToDelete = formulaConditionPair->second;

//            condToDelete->print(); cout << endl;
//            mpStateTree->print();

            eraseDTsOfRanking( *mpStateTree );
            assert( mpStateTree->substitutionResults().size() == 1 );
            assert( mpStateTree->substitutionResults().back().size() == 1 );
            ConditionVector& subResult = mpStateTree->rSubstitutionResults().back().back().first;
            auto cond = subResult.begin();
            while( cond != subResult.end() )
            {
                ConditionSet::iterator oCond = (*cond)->pOriginalConditions()->begin();
                while( oCond != (*cond)->originalConditions().end() )
                {
                    if( *oCond == condToDelete )
                    {
                        (*cond)->pOriginalConditions()->erase( oCond );
                        break;
                    }
                    ++oCond;
                }
                if( oCond != (*cond)->originalConditions().end() )
                {
                    cond = subResult.erase( cond );
                }
                else
                {
                    ++cond;
                }
            }
            mpStateTree->rSubResultsSimplified() = false;
            ConditionVector condsToDelete = ConditionVector();
            for( auto condition = mpStateTree->rConditions().begin(); condition != mpStateTree->conditions().end(); ++condition )
            {
                if( (*condition)->originalConditions().find( condToDelete ) != (*condition)->originalConditions().end() )
                {
                    condsToDelete.push_back( *condition );
                    break;
                }
            }
            mpStateTree->deleteConditions( condsToDelete );
            mpStateTree->rStateType() = COMBINE_SUBRESULTS;
            mpStateTree->rTakeSubResultCombAgain() = true;
            insertDTinRanking( mpStateTree );
            mFormulaConditionMap.erase( formulaConditionPair );
            delete condToDelete;
            mConditionsChanged = true;

//            mpStateTree->print();
        }
        Module::removeSubformula( _subformula );
    }

    /**
     * Checks the consistency of the so far received constraints.
     *
     * @return True,    if the so far received constraints are consistent;
     *         False,   if the so far received constraints are inconsistent;
     *         Unknown, if this module cannot determine whether the so far received constraints are consistent or not.
     */
    Answer VSModule::isConsistent()
    {
        if( mpReceivedFormula->isConstraintConjunction() )
        {
            assert( !(mpReceivedFormula->size() < mFormulaConditionMap.size()) );
            assert( !(mpReceivedFormula->size() > mFormulaConditionMap.size()) );
            if( !mConditionsChanged )
            {
                if( mInfeasibleSubsets.empty() )
                {
                    #ifdef VS_LOG_INTERMEDIATE_STEPS_OF_ASSIGNMENT
                    checkAnswer();
                    #endif
                    #ifdef VS_PRINT_ANSWERS
                    printAnswer();
                    #endif
                    mSolverState = True;
                    return True;
                }
                else
                {
                    mSolverState = False;
                    return False;
                }
            }
            mConditionsChanged = false;
            if( mpReceivedFormula->empty() )
            {
                #ifdef VS_LOG_INTERMEDIATE_STEPS_OF_ASSIGNMENT
                checkAnswer();
                #endif
                #ifdef VS_PRINT_ANSWERS
                printAnswer();
                #endif
                mSolverState = True;
                return True;
            }
            if( mInconsistentConstraintAdded )
            {
                assert( !mInfeasibleSubsets.empty() );
                assert( !mInfeasibleSubsets.back().empty() );
                mSolverState = False;
                return False;
            }

            while( !mRanking.empty() )
            {
                #ifdef VS_STATISTICS
                ++mStepCounter;
                #endif
                State* currentState = mRanking.begin()->second;
                if( currentState->hasChildrenToInsert() )
                {
                    currentState->rHasChildrenToInsert() = false;
                    insertDTsinRanking( currentState );
                }
                else
                {
                    #ifdef VS_DEBUG
                    cout << "Ranking:" << endl;
                    for( ValuationMap::const_iterator valDTPair = mRanking.begin(); valDTPair != mRanking.end(); ++valDTPair )
                    {
                        stringstream stream;
                        stream << "(" << valDTPair->first.first << ", " << valDTPair->first.second << ")";
                        cout << setw(15) << stream.str();
                        cout << ":  " << valDTPair->second << endl;
                    }
                    cout << "*** Considered state:" << endl;
                    currentState->printAlone( "*** ", cout );
                    #endif
                    currentState->simplify();
                    #ifdef VS_DEBUG
                    cout << "Simplifing results in " << endl;
                    currentState->printAlone( "*** ", cout );
                    #endif
                    if( currentState->isInconsistent() )
                    {
                        #ifdef VS_LOG_INTERMEDIATE_STEPS
                        logConditions( *currentState, false, "Intermediate_conflict_of_VSModule" );
                        #endif
                        eraseDTsOfRanking( *currentState );
                        if( currentState->isRoot() )
                        {
                            updateInfeasibleSubset();
                            mSolverState = False;
                            return False;
                        }
                        else
                        {
                            currentState->passConflictToFather();
                            eraseDTofRanking( currentState->rFather() );
                            insertDTinRanking( currentState->pFather() );
                        }
                    }
                    else if( currentState->hasRecentlyAddedConditions() )//&& !(currentState->takeSubResultCombAgain() && currentState->isRoot() ) )
                    {
                        #ifdef VS_DEBUG
                        cout << "*** Propagate new conditions :" << endl;
                        #endif
                        propagateNewConditions(currentState);
                        #ifdef VS_DEBUG
                        cout << "*** Propagate new conditions ready." << endl;
                        #endif
                    }
                    else
                    {
                        #ifdef VS_USE_VARIABLE_BOUNDS
                        if( !currentState->checkTestCandidatesForBounds() )
                        {
                            currentState->rInconsistent() = true;
                            eraseDTsOfRanking( *currentState );
                        }
                        else
                        {
                            #endif
                            switch( currentState->stateType() )
                            {
                                case SUBSTITUTION_TO_APPLY:
                                {
                                    #ifdef VS_DEBUG
                                    cout << "*** SubstituteAll changes it to:" << endl;
                                    #endif
                                    if( !substituteAll( currentState, currentState->rFather().rConditions() ) )
                                    {
                                        /*
                                        * Delete the currently considered state.
                                        */
                                        currentState->rInconsistent() = true;
                                        eraseDTofRanking( *currentState );
                                    }
                                    #ifdef VS_DEBUG
                                    cout << "*** SubstituteAll ready." << endl;
                                    #endif
                                    break;
                                }
                                case COMBINE_SUBRESULTS:
                                {
                                    #ifdef VS_DEBUG
                                    cout << "*** Refresh conditons:" << endl;
                                    #endif
                                    if( currentState->nextSubResultCombination() )
                                    {
                                        if( currentState->refreshConditions() )
                                        {
                                            insertDTinRanking( currentState );
                                        }
                                        else
                                        {
                                            insertDTsinRanking( currentState );
                                        }
                                        #ifdef VS_DEBUG
                                        currentState->printAlone( "   ", cout );
                                        #endif
                                    }
                                    else
                                    {
                                        /*
                                        * If it was the last combination, delete the state.
                                        */
                                        currentState->rInconsistent() = true;
                                        eraseDTsOfRanking( *currentState );
                                        currentState->rFather().rMarkedAsDeleted() = false;
                                        insertDTinRanking( currentState->pFather() );

                                    }
                                    #ifdef VS_DEBUG
                                    cout << "*** Conditions refreshed." << endl;
                                    #endif
                                    break;
                                }
                                case TEST_CANDIDATE_TO_GENERATE:
                                {
                                    /*
                                    * Set the index, if not already done, to the best variable to eliminate next.
                                    */
                                    if( currentState->index() == "" )
                                    {
                                        currentState->initIndex( mAllVariables );
                                    }
                                    else if( currentState->tryToRefreshIndex() )
                                    {
                                        if( currentState->initIndex( mAllVariables ) )
                                        {
                                            currentState->initConditionFlags();
                                            currentState->resetConflictSets();
                                            while( !currentState->children().empty() )
                                            {
                                                State* toDelete = currentState->rChildren().back();
                                                eraseDTsOfRanking( *toDelete );
                                                currentState->rChildren().pop_back();
                                                delete toDelete;
                                            }
                                        }
                                    }

                                    /*
                                    * Find the most adequate conditions to continue.
                                    */
                                    const vs::Condition* currentCondition;
                                    if( !currentState->bestCondition( currentCondition, mAllVariables.size() ) )
                                    {
                                        /*
                                        * It is a state, where no more elimination could be applied to the conditions.
                                        */
                                        if( currentState->conditions().empty() )
                                        {
                                            #ifdef VS_DEBUG
                                            cout << "*** Check ancestors!" << endl;
                                            #endif
                                            /*
                                            * Check if there are still conditions in any ancestor, which have not been considered.
                                            */
                                            State * unfinishedAncestor;
                                            if( currentState->unfinishedAncestor( unfinishedAncestor ) )
                                            {
                                                /*
                                                * Go back to this ancestor and refine.
                                                */
                                                eraseDTsOfRanking( *unfinishedAncestor );
                                                unfinishedAncestor->extendSubResultCombination();
                                                unfinishedAncestor->rStateType() = COMBINE_SUBRESULTS;
                                                if( unfinishedAncestor->refreshConditions() )
                                                {
                                                    insertDTinRanking( unfinishedAncestor );
                                                }
                                                else
                                                {
                                                    insertDTsinRanking( unfinishedAncestor );
                                                }
                                                #ifdef VS_DEBUG
                                                cout << "*** Found an unfinished ancestor:" << endl;
                                                unfinishedAncestor->printAlone();
                                                #endif
                                            }
                                            else
                                            {
                                                /*
                                                * Solution.
                                                */
                                                #ifdef VS_DEBUG
                                                printAll( cout );
                                                #endif
                                                #ifdef VS_LOG_INTERMEDIATE_STEPS_OF_ASSIGNMENT
                                                checkAnswer();
                                                #endif
                                                #ifdef VS_PRINT_ANSWERS
                                                printAnswer();
                                                #endif
                                                mSolverState = True;
                                                return True;
                                            }
                                        }
                                        /*
                                        * It is a state, where all conditions have been used for test candidate generation.
                                        */
                                        else
                                        {
                                            /*
                                            * Check whether there are still test candidates in form of children left.
                                            */
                                            bool                  currentStateHasChildrenToConsider       = false;
                                            bool                  currentStateHasChildrenWithToHighDegree = false;
                                            StateVector::iterator child                                   = currentState->rChildren().begin();
                                            while( child != currentState->children().end() )
                                            {
                                                if( !(**child).isInconsistent() )
                                                {
                                                    if( !(**child).markedAsDeleted() )
                                                    {
                                                        insertDTinRanking( *child );
                                                    }
                                                    if( !(**child).toHighDegree() && !(**child).markedAsDeleted() )
                                                    {
                                                        currentStateHasChildrenToConsider = true;
                                                    }
                                                    else
                                                    {
                                                        currentStateHasChildrenWithToHighDegree = true;
                                                    }
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
                                                    eraseDTsOfRanking( *currentState );
                                                    if( currentState->isRoot() )
                                                    {
                                                        updateInfeasibleSubset();
                                                    }
                                                    else
                                                    {
                                                        currentState->passConflictToFather();
                                                        eraseDTofRanking( currentState->rFather() );
                                                        insertDTinRanking( currentState->pFather() );
                                                    }
                                                }
                                                else
                                                {
                                                    currentState->rMarkedAsDeleted() = true;
                                                    eraseDTofRanking( *currentState );
                                                }
                                            }
                                        }
                                    }
                                    /*
                                    * Generate test candidates for the chosen variable and the chosen condition.
                                    */
                                    else
                                    {
                                        /*
                                        * The degree of the constraint is appropriate to applicate this version of the
                                        * virtual substitution.
                                        */
                                        symtab::const_iterator var = currentCondition->constraint().variables().find( currentState->index() );
                                        if( var != currentCondition->constraint().variables().end() )
                                        {
                                            #ifdef VS_DEBUG
                                            cout << "*** Eliminate " << currentState->index() << " in ";
                                            currentCondition->constraint().print( cout );
                                            cout << " creates:" << endl;
                                            #endif
                                            if( eliminate( currentState, currentState->index(), currentCondition ) )
                                            {
                                                #ifdef VS_DEBUG
                                                cout << "*** Eliminate ready." << endl;
                                                #endif
                                            }
                                            else
                                            {
                                                #ifdef VS_DEBUG
                                                cout << "*** No elimination. (Too high degree)" << endl;
                                                #endif
                                                if( (*currentState).toHighDegree() )
                                                {
                                                    /*
                                                    * If we need to involve a complete approach.
                                                    */
                                                    #ifdef VS_WITH_BACKEND
                                                    switch( runBackendSolvers( currentState ) )
                                                    {
                                                        case True:
                                                        {
                                                            currentState->rToHighDegree() = true;

                                                            State * unfinishedAncestor;
                                                            if( currentState->unfinishedAncestor( unfinishedAncestor ) )
                                                            {
                                                                /*
                                                                * Go back to this ancestor and refine.
                                                                */
                                                                eraseDTsOfRanking( *unfinishedAncestor );
                                                                unfinishedAncestor->extendSubResultCombination();
                                                                unfinishedAncestor->rStateType() = COMBINE_SUBRESULTS;
                                                                if( unfinishedAncestor->refreshConditions() )
                                                                {
                                                                    insertDTinRanking( unfinishedAncestor );
                                                                }
                                                                else
                                                                {
                                                                    insertDTsinRanking( unfinishedAncestor );
                                                                }
                                                            }
                                                            else
                                                            {
                                                                /*
                                                                * Solution.
                                                                */
                                                                #ifdef VS_DEBUG
                                                                printAll( cout );
                                                                #endif
                                                                #ifdef VS_LOG_INTERMEDIATE_STEPS_OF_ASSIGNMENT
                                                                checkAnswer();
                                                                #endif
                                                                #ifdef VS_PRINT_ANSWERS
                                                                printAnswer();
                                                                #endif
                                                                mSolverState = True;
                                                                return True;
                                                            }
                                                            break;
                                                        }
                                                        case False:
                                                        {
                                                            break;
                                                        }
                                                        case Unknown:
                                                        {
                                                            mSolverState = Unknown;
                                                            return Unknown;
                                                        }
                                                        default:
                                                        {
                                                            cout << "Error: Unknown answer in method " << __func__ << " line " << __LINE__ << endl;
                                                            mSolverState = Unknown;
                                                            return Unknown;
                                                        }
                                                    }
                                                    #else
    //                                                currentState->printAlone( "   ", cout );
    //                                                cout << "###" << endl;
    //                                                cout << "###                  Unknown!" << endl;
    //                                                cout << "###" << endl;
    //                                                mDeductions.clear();
                                                    mSolverState = Unknown;
                                                    return Unknown;
                                                    #endif
                                                }
                                                else
                                                {
                                                    currentState->rToHighDegree() = true;
                                                    insertDTinRanking( currentState );
                                                }
                                            }
                                        }
                                        else
                                        {
                                            (*currentCondition).rFlag() = true;
                                            /*
                                            * Update the ranking entry of the state.
                                            */
                                            insertDTinRanking( currentState );
                                        }
                                    }
                                    break;
                                }
                                default:
                                    assert( false );
                            }
                            #ifdef VS_USE_VARIABLE_BOUNDS
                        }
                        #endif
                    }
                }
            }
            // if( mpStateTree->conflictSets().empty() ) mpStateTree->print();
            // #ifdef VS_LOG_INTERMEDIATE_STEPS
            // if( mpStateTree->conflictSets().empty() ) logConditions( *mpStateTree, false, "Intermediate_conflict_of_VSModule" );
            // #endif
            // if( mpStateTree->conflictSets().empty() ) Module::storeAssumptionsToCheck( *mpManager );
            assert( !mpStateTree->conflictSets().empty() );
            updateInfeasibleSubset();
            #ifdef VS_DEBUG
            printAll( cout );
            #endif
            mSolverState = False;
            return False;
        }
        else
        {
            return Unknown;
        }
    }

    /**
     *
     */
    void VSModule::updateModel()
    {
        mModel.clear();
        if( mSolverState == True )
        {
            assert( !mRanking.empty() );
            const State* state = mRanking.begin()->second;
            while( !state->isRoot() )
            {
                stringstream outA;
                const Substitution& sub = state->substitution();
                if( sub.type() == ST_MINUS_INFINITY )
                {
                    outA << "-inf_" << mId << "_" << state->treeDepth();
                }
                else
                {
                    outA << sub.term().expression().expand().normal();
                    if( sub.type() == ST_PLUS_EPSILON )
                    {
                        outA << "+eps_" << mId << "_" << state->treeDepth();
                    }
                }
                mModel.insert( pair< const string, string >( state->substitution().variable(), outA.str() ) );
                state = state->pFather();
            }
            if( mRanking.begin()->second->toHighDegree() )
            {
                Module::getBackendsModel();
            }
        }
    }

    /**
     * Eliminates the given variable by finding test candidates of the constraint of the given
     * condition. All this happens in the state _currentState.
     *
     * @param _currentState     The currently considered state.
     * @param _eliminationVar   The substitution to apply.
     * @param _condition        The condition with the constraint, in which should be substituted.
     *
     * @sideeffect: For each test candidate a new child of the currently considered state
     *              is generated. The solved constraint in the currently considered
     *              state is now labeled by true, which means, that the constraint
     *              already served to eliminate for the respective variable in this
     *              state.
     */
    bool VSModule::eliminate( State* _currentState, const string& _eliminationVar, const vs::Condition* _condition )
    {
        /*
         * Get the constraint of this condition.
         */
        const Constraint& constraint = (*_condition).constraint();

        /*
         * Get coefficients of the variable in the constraints.
         */
        symbol sym;
        constraint.variable( _eliminationVar, sym );
        symtab vars = symtab( constraint.variables() );
        vars.erase( _eliminationVar );

        /*
         * Determine the substitution type: normal or +epsilon
         */
        Substitution_Type subType = ST_PLUS_EPSILON;
        if( constraint.relation() == CR_EQ || constraint.relation() == CR_LEQ || constraint.relation() == CR_GEQ )
        {
            subType = ST_NORMAL;
        }

        vector<ex> coeffs = vector<ex>();
        #ifdef VS_ELIMINATE_MULTI_ROOTS
        signed degree = constraint.multiRootLessLhs().degree( ex( sym ) );
        #else
        signed degree = constraint.lhs().degree( ex( sym ) );
        #endif
        for( signed i = 0; i <= degree; ++i )
        {
            #ifdef VS_ELIMINATE_MULTI_ROOTS
            coeffs.push_back( ex( constraint.multiRootLessLhs().coeff( ex( sym ), i ) ) );
            #else
            coeffs.push_back( ex( constraint.lhs().coeff( ex( sym ), i ) ) );
            #endif
        }

        ConditionSet oConditions = ConditionSet();
        oConditions.insert( _condition );

        bool     generatedTestCandidateBeingASolution = false;
        unsigned numberOfAddedChildren                = 0;

        /*
         * Generate test candidates for the chosen variable considering the chosen constraint.
         */
        switch( coeffs.size() )
        {
            case 1:
            {
                assert( false );
                return false;
            }
            //degree = 1
            case 2:
            {
                /*
                 * Create state ({b!=0} + oldConditions, [x -> -c/b]):
                 */
                if( (*_currentState).addChild( coeffs.at( 1 ), CR_NEQ, _eliminationVar, sym, -coeffs.at( 0 ), 0, coeffs.at( 1 ), 0, subType, vars,
                                               oConditions ) )
                {
                    if( constraint.relation() == CR_EQ )
                    {
                        if( coeffs.at( 1 ).info( info_flags::rational ) )
                        {
                            _currentState->rChildren().back()->setOriginalCondition( _condition );
                            generatedTestCandidateBeingASolution = true;
                        }
                    }

                    /*
                     * Add its valuation to the current ranking.
                     */
                    insertDTinRanking( (*_currentState).rChildren().back() );
                    ++numberOfAddedChildren;
                    #ifdef VS_DEBUG
                    (*(*_currentState).rChildren().back()).print( "   ", cout );
                    #endif
                }
                else if( constraint.relation() == CR_EQ && coeffs.at( 1 ).info( info_flags::rational ) )
                {
                    generatedTestCandidateBeingASolution = true;
                }
                break;
            }
            //degree = 2
            case 3:
            {
                ex radicand = ex( pow( coeffs.at( 1 ), 2 ) - 4 * coeffs.at( 2 ) * coeffs.at( 0 ) );
                Constraint::normalize( radicand );

                /*
                 * Create state ({a==0, b!=0} + oldConditions, [x -> -c/b]):
                 */
                if( (*_currentState).addChild( coeffs.at( 2 ), CR_EQ, coeffs.at( 1 ), CR_NEQ, _eliminationVar, sym, -coeffs.at( 0 ), 0,
                                               coeffs.at( 1 ), 0, subType, vars, oConditions ) )
                {
                    if( constraint.relation() == CR_EQ )
                    {
                        if( coeffs.at( 2 ).info( info_flags::rational ) && coeffs.at( 1 ).info( info_flags::rational ) )
                        {
                            _currentState->rChildren().back()->setOriginalCondition( _condition );
                            generatedTestCandidateBeingASolution = true;
                        }
                    }

                    /*
                     * Add its valuation to the current ranking.
                     */
                    insertDTinRanking( (*_currentState).rChildren().back() );
                    ++numberOfAddedChildren;
                    #ifdef VS_DEBUG
                    (*(*_currentState).rChildren().back()).print( "   ", cout );
                    #endif
                }

                /*
                 * Create state ({a!=0, b^2-4ac>=0} + oldConditions, [x -> (-b+sqrt(b^2-4ac))/2a]):
                 */
                if( (*_currentState).addChild( coeffs.at( 2 ), CR_NEQ, radicand, CR_GEQ, _eliminationVar, sym, -coeffs.at( 1 ), 1,
                                               2 * coeffs.at( 2 ), radicand, subType, vars, oConditions ) )
                {
                    if( constraint.relation() == CR_EQ )
                    {
                        if( coeffs.at( 2 ).info( info_flags::rational ) && radicand.info( info_flags::rational ) )
                        {
                            _currentState->rChildren().back()->setOriginalCondition( _condition );
                            generatedTestCandidateBeingASolution = true;
                        }
                    }

                    /*
                     * Add its valuation to the current ranking.
                     */
                    insertDTinRanking( (*_currentState).rChildren().back() );
                    ++numberOfAddedChildren;
                    #ifdef VS_DEBUG
                    (*(*_currentState).rChildren().back()).print( "   ", cout );
                    #endif
                }

                /*
                 * Create state ({a!=0, b^2-4ac>=0} + oldConditions, [x -> (-b-sqrt(b^2-4ac))/2a]):
                 */
                if( (*_currentState).addChild( coeffs.at( 2 ), CR_NEQ, radicand, CR_GEQ, _eliminationVar, sym, -coeffs.at( 1 ), -1,
                                               2 * coeffs.at( 2 ), radicand, subType , vars, oConditions ) )
                {
                    if( constraint.relation() == CR_EQ )
                    {
                        if( coeffs.at( 2 ).info( info_flags::rational ) && radicand.info( info_flags::rational ) )
                        {
                            _currentState->rChildren().back()->setOriginalCondition( _condition );
                            generatedTestCandidateBeingASolution = true;
                        }
                    }

                    /*
                     * Add its valuation to the current ranking.
                     */
                    insertDTinRanking( (*_currentState).rChildren().back() );
                    ++numberOfAddedChildren;
                    #ifdef VS_DEBUG
                    (*(*_currentState).rChildren().back()).print( "   ", cout );
                    #endif
                }

                if( numberOfAddedChildren == 0 && constraint.relation() == CR_EQ && coeffs.at( 2 ).info( info_flags::rational ) && coeffs.at( 1 ).info( info_flags::rational ) )
                {
                    generatedTestCandidateBeingASolution = true;
                }
                break;
            }
            #ifdef VS_CUBIC_CASE
            //degree = 3
            case 4:
            {
                break;
            }
            #endif
            //degree > 2 (> 3)
            default:
            {
                return false;
            }
        }

        if( !generatedTestCandidateBeingASolution )
        {
            /*
             * Create state ( Conditions, [x -> -infinity]):
             */
            if( (*_currentState).addChild( _eliminationVar, sym, ST_MINUS_INFINITY, oConditions ) )
            {
                /*
                 * Add its valuation to the current ranking.
                 */
                insertDTinRanking( (*_currentState).rChildren().back() );
                numberOfAddedChildren++;
                #ifdef VS_DEBUG
                (*(*_currentState).rChildren().back()).print( "   ", cout );
                #endif
            }
        }
        if( generatedTestCandidateBeingASolution )
        {
            for( ConditionVector::iterator cond = _currentState->rConditions().begin(); cond != _currentState->conditions().end(); ++cond )
            {
                (**cond).rFlag() = true;
            }
            assert( numberOfAddedChildren <= _currentState->children().size() );

            if( numberOfAddedChildren == 0 )
            {
                ConditionSetSet conflictSet = ConditionSetSet();
                ConditionSet condSet  = ConditionSet();
                condSet.insert( _condition );
                conflictSet.insert( condSet );
                _currentState->addConflicts( NULL, conflictSet );
                _currentState->rInconsistent() = true;
            }
            else
            {
                while( _currentState->children().size() > numberOfAddedChildren )
                {
                    State* toDelete = *_currentState->rChildren().begin();
    //                ConflictSets::iterator conflictSet = _currentState->rConflictSets().find( toDelete->pSubstitution() );
    //                if( conflictSet != _currentState->conflictSets().end() )
    //                {
    //                    _currentState->rConflictSets().erase( conflictSet );
    //                }
                    _currentState->resetConflictSets();
                    _currentState->rChildren().erase( _currentState->rChildren().begin() );
                    delete toDelete;
                }
            }
        }
        else
        {
            (*_condition).rFlag() = true;
        }

        insertDTinRanking( _currentState );

        return true;
    }

    /**
     * Applies the substitution of _currentState to the given conditions.
     *
     * @param _currentState     The currently considered state.
     * @param _conditions       The conditions to which the substitution in this state
     *                          shall be applied. Note that these conditions are always
     *                          a subset of the condition vector in the father of this
     *                          state.
     *
     * @sideeffect: The result is stored in the substitution result of the given state.
     */
    bool VSModule::substituteAll( State* _currentState, ConditionVector& _conditions )
    {
        /*
         * Create a vector to store the results of each single substitution. Each entry corresponds to
         * the results of a single substitution. These results can be considered as a disjunction of
         * conjunctions of constraints.
         */
        vector<DisjunctionOfConditionConjunctions> disjunctionsOfCondConj;
        disjunctionsOfCondConj = vector<DisjunctionOfConditionConjunctions>();

        /*
         * The substitution to apply.
         */
        assert( !_currentState->isRoot() );
        const Substitution& currentSubstitution = _currentState->substitution();

        /*
         * The variable to substitute.
         */
        const string& substitutionVariable = currentSubstitution.variable();

        /*
         * The conditions of the currently considered state, without
         * the one getting just eliminated.
         */
        ConditionVector oldConditions = ConditionVector();

        bool anySubstitutionFailed = false;
        ConditionSetSet conflictSet = ConditionSetSet();

        /*
         * Apply the most recent substitution in this state to each of its conditions.
         */
        for( ConditionVector::iterator cond = _conditions.begin(); cond != _conditions.end(); ++cond )
        {
            /*
             * The constraint to substitute in.
             */
            const Constraint* currentConstraint = (**cond).pConstraint();

            /*
             * Does the condition contain the variable to substitute.
             */
            symtab::const_iterator var = currentConstraint->variables().find( substitutionVariable );
            if( var == currentConstraint->variables().end() )
            {
                if( !anySubstitutionFailed )
                {
                    /*
                     * If the variable to substitute does not occur in the condition,
                     * add the condition to the vector of conditions we just add to the
                     * states we create.
                     */
                    oldConditions.push_back( new vs::Condition( currentConstraint, (**cond).valuation() ) );
                    oldConditions.back()->pOriginalConditions()->insert( *cond );
                }
            }
            else
            {
                /*
                 * Apply the substitution to each condition, in which the variable to substitute
                 * occurs and collect the results.
                 */
                DisjunctionOfConstraintConjunctions disjunctionOfConsConj;
                disjunctionOfConsConj = DisjunctionOfConstraintConjunctions();
                substitute( currentConstraint, currentSubstitution, disjunctionOfConsConj );

                /*
                 * Create the the conditions according to the just created constraint prototypes.
                 */
                bool anyConjunctionConsistent = false;
                disjunctionsOfCondConj.push_back( DisjunctionOfConditionConjunctions() );
                DisjunctionOfConditionConjunctions& currentDisjunction = disjunctionsOfCondConj.back();
                for( DisjunctionOfConstraintConjunctions::iterator consConj = disjunctionOfConsConj.begin(); consConj != disjunctionOfConsConj.end();
                        ++consConj )
                {
                    bool conjunctionConsistent = true;
                    /*
                     * Check if the conjunction contains any inconsistent constraint.
                     */
                    for( TS_ConstraintConjunction::iterator cons = consConj->begin(); cons != consConj->end(); ++cons )
                    {
                        if( (**cons).isConsistent() == 0 )
                        {
                            conjunctionConsistent = false;
                            break;
                        }
                    }
                    if( conjunctionConsistent )
                    {
                        anyConjunctionConsistent = true;
                        if( !anySubstitutionFailed )
                        {
                            currentDisjunction.push_back( ConditionVector() );
                            ConditionVector& currentConjunction = currentDisjunction.back();
                            for( TS_ConstraintConjunction::iterator cons = consConj->begin(); cons != consConj->end(); ++cons )
                            {
                                /*
                                 * Add all conditions to the conjunction, which are not variable-free and consistent.
                                 */
                                if( (**cons).isConsistent() != 1 )
                                {
                                    currentConjunction.push_back( new vs::Condition( *cons, _currentState->treeDepth() ) );
                                    currentConjunction.back()->pOriginalConditions()->insert( *cond );
                                }
                            }
                        }
                        else
                            break;
                    }
                }
                if( !anyConjunctionConsistent )
                {
                    anySubstitutionFailed = true;
                    ConditionSet condSet  = ConditionSet();
                    condSet.insert( *cond );
                    if( _currentState->pOriginalCondition() != NULL )
                    {
                        condSet.insert( _currentState->pOriginalCondition() );
                    }
                    conflictSet.insert( condSet );
                }
            }
        }
        if( anySubstitutionFailed )
        {
            _currentState->rFather().addConflicts( _currentState->pSubstitution(), conflictSet );
            _currentState->rInconsistent() = true;

            /*
             * Delete the conflict sets of this state.
             */
            _currentState->resetConflictSets();

            /*
             * Delete the children of this state.
             */
            while( !_currentState->children().empty() )
            {
                State* toDelete = _currentState->rChildren().back();
                _currentState->rChildren().pop_back();
                delete toDelete;
            }


            /*
             * Delete the conditions of this state.
             */
            while( !_currentState->conditions().empty() )
            {
                const vs::Condition* pCond = _currentState->rConditions().back();
                _currentState->rConditions().pop_back();
                #ifdef VS_USE_VARIABLE_BOUNDS
                _currentState->rVariableBounds().removeBound( pCond->pConstraint(), pCond );
                #endif
                delete pCond;
            }

            /*
             * Delete the everything in oldConditions.
             */
            while( !oldConditions.empty() )
            {
                const vs::Condition* rpCond = oldConditions.back();
                oldConditions.pop_back();
                delete rpCond;
            }

            /*
             * Delete the everything in disjunctionsOfCondConj.
             */
            while( !disjunctionsOfCondConj.empty() )
            {
                while( !disjunctionsOfCondConj.back().empty() )
                {
                    while( !disjunctionsOfCondConj.back().back().empty() )
                    {
                        const vs::Condition* rpCond = disjunctionsOfCondConj.back().back().back();
                        disjunctionsOfCondConj.back().back().pop_back();
                        delete rpCond;
                    }
                    disjunctionsOfCondConj.back().pop_back();
                }
                disjunctionsOfCondConj.pop_back();
            }
            return false;
        }
        else
        {
            disjunctionsOfCondConj.push_back( DisjunctionOfConditionConjunctions() );
            disjunctionsOfCondConj.back().push_back( oldConditions );
            _currentState->addSubstitutionResults( disjunctionsOfCondConj );
            if( !_currentState->isInconsistent() )
            {
                insertDTinRanking( _currentState );
            }
            #ifdef VS_DEBUG
            _currentState->print( "   ", cout );
            #endif
            return true;
        }
    }

    /**
     * Applies the substitution of the given state to all conditions, which were recently added to it.
     *
     * @param _currentState The currently considered state.
     */
    void VSModule::propagateNewConditions( State* _currentState )
    {
        eraseDTsOfRanking( *_currentState );
        _currentState->rHasRecentlyAddedConditions() = false;
        if( _currentState->takeSubResultCombAgain() && _currentState->stateType() == COMBINE_SUBRESULTS )
        {
            #ifdef VS_DEBUG
            cout << "*** Refresh conditons:" << endl;
            #endif
            _currentState->refreshConditions();
            _currentState->rTakeSubResultCombAgain() = false;
            #ifdef VS_DEBUG
            _currentState->printAlone( "   ", cout );
            cout << "*** Conditions refreshed." << endl;
            #endif
        }

        /*
         * Collect the recently added conditions and mark them as not recently added.
         */
        bool deleteExistingTestCandidates = false;
        ConditionVector recentlyAddedConditions = ConditionVector();
        for( ConditionVector::iterator cond = _currentState->rConditions().begin(); cond != _currentState->conditions().end(); ++cond )
        {
            if( (**cond).recentlyAdded() )
            {
                (**cond).rRecentlyAdded() = false;
                recentlyAddedConditions.push_back( *cond );
                if( _currentState->pOriginalCondition() == NULL )
                {
                    if( (**cond).constraint().hasFinitelyManySolutionsIn( _currentState->index() ) )
                    {
                        deleteExistingTestCandidates = true;
                    }
                }
            }
        }

        insertDTinRanking( _currentState );

        if( !_currentState->children().empty() )
        {
            if( deleteExistingTestCandidates || _currentState->initIndex( mAllVariables ) )
            {
                _currentState->initConditionFlags();

                /*
                 * If the recently added conditions make another variable being the best to eliminate next
                 * delete all children.
                 */
                _currentState->resetConflictSets();
                while( !_currentState->children().empty() )
                {
                    State* toDelete = _currentState->rChildren().back();
                    _currentState->rChildren().pop_back();
                    delete toDelete;
                }
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
                    for( ConditionVector::iterator cond = recentlyAddedConditions.begin(); cond != recentlyAddedConditions.end(); ++cond )
                    {
                        if( (**cond).constraint().hasVariable( _currentState->index() ) )
                        {
                            bool                  worseConditionFound = false;
                            StateVector::iterator child               = _currentState->rChildren().begin();
                            while( !worseConditionFound && child != _currentState->children().end() )
                            {
                                if( (**child).substitution().type() != ST_MINUS_INFINITY )
                                {
                                    ConditionSet::iterator oCond = (**child).rSubstitution().rOriginalConditions().begin();
                                    while( !worseConditionFound && oCond != (**child).substitution().originalConditions().end() )
                                    {
                                        if( (**cond).valuate( _currentState->index(), mAllVariables.size(), true )
                                                > (**oCond).valuate( _currentState->index(), mAllVariables.size(), true ) )
                                        {
                                            newTestCandidatesGenerated = true;
                                            #ifdef VS_DEBUG
                                            cout << "*** Eliminate " << _currentState->index() << " in ";
                                            (**cond).constraint().print( cout );
                                            cout << " creates:" << endl;
                                            #endif
                                            eliminate( _currentState, _currentState->index(), *cond );
                                            #ifdef VS_DEBUG
                                            cout << "*** Eliminate ready." << endl;
                                            #endif
                                            worseConditionFound = true;
                                            break;
                                        }
                                        ++oCond;
                                    }
                                }
                                ++child;
                            }
                        }
                    }
                }

                /*
                 * Otherwise, add the recently added conditions to each child of the considered state to
                 * which a substitution must be or already has been applied.
                 */
                for( StateVector::iterator child = _currentState->rChildren().begin(); child != _currentState->children().end(); ++child )
                {
                    if( (**child).stateType() != SUBSTITUTION_TO_APPLY || (**child).isInconsistent() )
                    {
                        /*
                         * Apply substitution to new conditions and add the result to the substitution result vector.
                         */
                        substituteAll( *child, recentlyAddedConditions );
                        if( (**child).isInconsistent() &&!(**child).subResultsSimplified() )
                        {
                            (**child).simplify();
                            if( !(**child).conflictSets().empty() )
                            {
                                insertDTinRanking( *child );
                            }
                        }
                    }
                    else
                    {
                        if( newTestCandidatesGenerated )
                        {
                            insertDTinRanking( *child );
                            if( !(**child).children().empty() )
                            {
                                (**child).rHasChildrenToInsert() = true;
                            }
                        }
                        else
                        {
                            insertDTsinRanking( *child );
                        }
                    }
                }
            }
        }
    }

    /**
     * Increases the ID-allocator.
     */
    void VSModule::increaseIDCounter()
    {
        if( mIDCounter == MAX_ID )
        {
            mIDCounter = 1;
            cout << "Warning: Already allocated last ID." << endl;
        }
        else
        {
            mIDCounter++;
        }
    }

    /**
     * Inserts a state in the ranking.
     *
     * @param _state The states, which will be inserted.
     */
    void VSModule::insertDTinRanking( State* _state )
    {
        if( !_state->markedAsDeleted() && !(_state->isInconsistent() && _state->conflictSets().empty() && _state->conditionsSimplified()) )
        {
            if( _state->id() != 0 )
            {
                unsigned id = _state->id();
                eraseDTofRanking( *_state );
                _state->setID( id );
            }
            else
            {
                increaseIDCounter();
                _state->setID( mIDCounter );
            }

            _state->updateValuation();

            if( (mRanking.insert( ValStatePair( _state->valuationPlusID(), _state ) )).second == false )
            {
                cout << "Warning: Could not insert. Entry already exists.";
                cout << endl;
            }
        }
    }

    /**
     * Inserts a state and all its successors in the ranking.
     *
     * @param _state The root of the states, which will be inserted.
     */
    void VSModule::insertDTsinRanking( State* _state )
    {
        insertDTinRanking( _state );

        if( _state->conditionsSimplified() && _state->subResultsSimplified() && !_state->takeSubResultCombAgain() && !_state->hasRecentlyAddedConditions() )
        {
            for( StateVector::iterator dt = (*_state).rChildren().begin(); dt != (*_state).children().end(); ++dt )
            {
                insertDTsinRanking( *dt );
            }
        }
    }

    /**
     * Erases a state of the ranking.
     *
     * @param _state The states, which will be erased of the ranking.
     *
     * @return  True, if the state was in the ranking.
     */
    bool VSModule::eraseDTofRanking( State& _state )
    {
        ValuationMap::iterator valDTPair = mRanking.find( _state.valuationPlusID() );
        if( valDTPair != mRanking.end() )
        {
            mRanking.erase( valDTPair );
            _state.setID( 0 );
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * Erases a state and its successors of the ranking.
     *
     * @param _state The root of the states, which will be erased of the ranking.
     */
    void VSModule::eraseDTsOfRanking( State& _state )
    {
        eraseDTofRanking( _state );

        for( StateVector::iterator dt = _state.rChildren().begin(); dt != _state.children().end(); ++dt )
        {
            eraseDTsOfRanking( **dt );
        }
    }

    /**
     * Updates the infeasible subset.
     */
    void VSModule::updateInfeasibleSubset()
    {
        #ifdef VS_INFEASIBLE_SUBSET_GENERATION
        /*
         * Determine the minimum covering sets of the conflict sets, i.e. the infeasible subsets of the root.
         */
        ConditionSetSet minCoverSets = ConditionSetSet();
        ConditionSetSetSet confSets  = ConditionSetSetSet();
        ConflictSets::iterator nullConfSet = mpStateTree->rConflictSets().find( NULL );
        if( nullConfSet != mpStateTree->rConflictSets().end() )
        {
            confSets.insert( nullConfSet->second.begin(), nullConfSet->second.end() );
        }
        else
        {
            for( ConflictSets::iterator confSet = mpStateTree->rConflictSets().begin(); confSet != mpStateTree->rConflictSets().end(); ++confSet )
            {
                confSets.insert( confSet->second.begin(), confSet->second.end() );
            }
        }
        allMinimumCoveringSets( confSets, minCoverSets );
        if( minCoverSets.empty() )
        {
            printAll();
        }
        assert( !minCoverSets.empty() );

        /*
         * Change the globally stored infeasible subset to the smaller one.
         */
        mInfeasibleSubsets.clear();
        for( ConditionSetSet::const_iterator minCoverSet = minCoverSets.begin(); minCoverSet != minCoverSets.end(); ++minCoverSet )
        {
            assert( !minCoverSet->empty() );
            mInfeasibleSubsets.push_back( set<const Formula*>() );
            for( ConditionSet::const_iterator cond = minCoverSet->begin(); cond != minCoverSet->end(); ++cond )
            {
                for( ConditionSet::const_iterator oCond = (**cond).originalConditions().begin(); oCond != (**cond).originalConditions().end();
                        ++oCond )
                {
                    Formula::const_iterator receivedConstraint = mpReceivedFormula->begin();
                    while( receivedConstraint != mpReceivedFormula->end() )
                    {
                        if( (**oCond).constraint() == (*receivedConstraint)->constraint() )
                        {
                            break;
                        }
                        receivedConstraint++;
                    }
                    assert( receivedConstraint != mpReceivedFormula->end() );
                    mInfeasibleSubsets.back().insert( *receivedConstraint );
                }
            }
        }
        assert( !mInfeasibleSubsets.empty() );
        assert( !mInfeasibleSubsets.back().empty() );
        #else
        /*
         * Set the infeasible subset to the set of all received constraints.
         */
        mInfeasibleSubsets.push_back( set<const Formula*>() );
        for( Formula::const_iterator cons = receivedFormulaBegin(); cons != receivedFormulaEnd(); ++cons )
        {
            mInfeasibleSubsets.back().insert( *cons );
        }
        #endif
    }

    /**
     * Gets a symbolic assignment, if an assignment exists and the consistency check determined
     * the satisfiability of the given set of constraints.
     *
     * @return A symbolic assignment.
     */
    vector<pair<string, pair<Substitution_Type, ex> > > VSModule::getSymbolicAssignment() const
    {
        assert( !mConditionsChanged && mInfeasibleSubsets.empty() );
        vector<pair<string, pair<Substitution_Type, ex> > > result    = vector<pair<string, pair<Substitution_Type, ex> > >();
        vector<pair<string, pair<Substitution_Type, ex> > > resultTmp = vector<pair<string, pair<Substitution_Type, ex> > >();
        symtab uncheckedVariables = mAllVariables;
        const State* currentState = mRanking.begin()->second;
        while( !currentState->isRoot() )
        {
            const Substitution& sub = currentState->substitution();
            uncheckedVariables.erase( sub.variable() );
            pair<Substitution_Type, ex>                symValue        = pair<Substitution_Type, ex>( sub.type(), sub.term().expression() );
            pair<string, pair<Substitution_Type, ex> > symVarValuePair = pair<string, pair<Substitution_Type, ex> >( sub.variable(), symValue );
            resultTmp.push_back( symVarValuePair );
            currentState = (*currentState).pFather();
        }
        for( symtab::const_iterator var = uncheckedVariables.begin(); var != uncheckedVariables.end(); ++var )
        {
            pair<Substitution_Type, ex>                symValue        = pair<Substitution_Type, ex>( ST_NORMAL, 0 );
            pair<string, pair<Substitution_Type, ex> > symVarValuePair = pair<string, pair<Substitution_Type, ex> >( var->first, symValue );
            result.push_back( symVarValuePair );
        }
        result.insert( result.end(), resultTmp.begin(), resultTmp.end() );
        return result;
    }

    /**
     * Finds all minimum covering sets of a vector of sets of sets. A minimum covering set
     * fulfills the following properties:
     *
     *          1.) It covers in each set of sets at least one of its sets.
     *          2.) If you delete any element of the minimum covering set, the
     *              first property does not hold anymore.
     *
     * @param _conflictSets     The vector of sets of sets, for which the method finds all minimum covering sets.
     * @param _minCovSets   The resulting minimum covering sets.
     */
    void VSModule::allMinimumCoveringSets( const ConditionSetSetSet& _conflictSets, ConditionSetSet& _minCovSets )
    {
        if( !_conflictSets.empty() )
        {
            /*
             * First we construct all possible combinations of combining all single sets of each set of sets.
             * Store for each set an iterator.
             */
            vector<ConditionSetSet::iterator> conditionSetSetIters = vector<ConditionSetSet::iterator>();
            for( ConditionSetSetSet::const_iterator conflictSet = _conflictSets.begin(); conflictSet != _conflictSets.end(); ++conflictSet )
            {
                conditionSetSetIters.push_back( (*conflictSet).begin() );

                /*
                 * Assure, that the set is not empty.
                 */
                assert( conditionSetSetIters.back() != (*conflictSet).end() );
            }
            ConditionSetSetSet::iterator                conflictSet;
            vector<ConditionSetSet::iterator>::iterator conditionSet;

            /*
             * Find all covering sets by forming the union of all combinations.
             */
            bool lastCombinationReached = false;
            while( !lastCombinationReached )
            {
                /*
                 * Create a new combination of vectors.
                 */
                ConditionSet coveringSet = ConditionSet();

                bool previousIteratorIncreased = false;

                /*
                 * For each set of sets in the vector of sets of sets, choose a set in it. We combine
                 * these sets by forming their union and store it as a covering set.
                 */
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

                        /*
                         * Set the iterator.
                         */
                        if( !previousIteratorIncreased )
                        {
                            (*conditionSet)++;
                            if( *conditionSet != (*conflictSet).end() )
                            {
                                previousIteratorIncreased = true;
                            }
                            else
                            {
                                *conditionSet = (*conflictSet).begin();
                            }
                        }
                        conflictSet++;
                        conditionSet++;
                        if( !previousIteratorIncreased && conditionSet == conditionSetSetIters.end() )
                        {
                            lastCombinationReached = true;
                        }
                    }
                }
                _minCovSets.insert( coveringSet );
            }

            /*
             * Delete all covering sets, which are not minimal. We benefit of the set of sets property,
             * which sorts its sets according to the elements they contain. If a set M is a subset of
             * another set M', the position of M in the set of sets is before M'.
             */
            ConditionSetSet::iterator minCoverSet = _minCovSets.begin();
            ConditionSetSet::iterator coverSet    = _minCovSets.begin();
            coverSet++;

            while( coverSet != _minCovSets.end() )
            {
                ConditionSet::iterator cond1 = (*minCoverSet).begin();
                ConditionSet::iterator cond2 = (*coverSet).begin();
                while( cond1 != (*minCoverSet).end() && cond2 != (*coverSet).end() )
                {
                    if( *cond1 != *cond2 )
                    {
                        break;
                    }
                    cond1++;
                    cond2++;
                }
                if( cond1 == (*minCoverSet).end() )
                {
                    _minCovSets.erase( coverSet++ );
                }
                else
                {
                    minCoverSet = coverSet;
                    coverSet++;
                }
            }
        }
    }

    /**
     * Adapts the passed formula according to the conditions of the currently considered state.
     *
     * @return  true,   if the passed formula has been changed;
     *          false,  otherwise.
     */
    bool VSModule::adaptPassedFormula( const State& _state )
    {
        bool changedPassedFormula = false;

        /*
         * Collect the constraints to check.
         */
        set<Constraint> constraintsToCheck = set<Constraint>();
        for( ConditionVector::const_iterator cond = _state.conditions().begin(); cond != _state.conditions().end(); ++cond )
        {
            constraintsToCheck.insert( (**cond).constraint() );
        }

        /*
         * Remove the constraints from the constraints to check, which are already in the passed formula
         * and remove the sub formulas (constraints) in the passed formula, which do not occur in the
         * constraints to add.
         */
        Formula::iterator subformula = mpPassedFormula->begin();
        while( subformula != mpPassedFormula->end() )
        {
            if( constraintsToCheck.erase( (*subformula)->constraint() ) == 0 )
            {
                subformula           = removeSubformulaFromPassedFormula( subformula );
                changedPassedFormula = true;
            }
            else
            {
                ++subformula;
            }
        }

        /*
         * Add the the remaining constraints to add to the passed formula.
         */
        for( set<Constraint>::iterator iter = constraintsToCheck.begin(); iter != constraintsToCheck.end(); ++iter )
        {
            changedPassedFormula           = true;
            vec_set_const_pFormula origins = vec_set_const_pFormula();
            addSubformulaToPassedFormula( new smtrat::Formula( smtrat::Formula::newConstraint( iter->lhs(), iter->relation(), iter->variables() ) ), origins );
        }
        return changedPassedFormula;
    }

    /**
     * Run the backend solvers on the conditions of the given state.
     *
     * @param _state    The state to check the conditions of.
     *
     * @return  TS_True,    if the conditions are consistent and there is no unfinished ancestor;
     *          TS_False,   if the conditions are inconsistent;
     *          TS_Unknown, if the theory solver cannot give an answer for these conditons.
     */
    Answer VSModule::runBackendSolvers( State* _state )
    {
        /*
         * Run the backends on the constraint of the state.
         */
        adaptPassedFormula( *_state );

        switch( runBackends() )
        {
            case True:
            {
                return True;
            }
            case False:
            {
                /*
                * Get the conflict sets formed by the infeasible subsets in the backend.
                */
                ConditionSetSet conflictSet = ConditionSetSet();
                vector<Module*>::const_iterator backend = usedBackends().begin();
                while( backend != usedBackends().end() )
                {
                    if( !(*backend)->infeasibleSubsets().empty() )
                    {
                        for( vec_set_const_pFormula::const_iterator infsubset = (*backend)->infeasibleSubsets().begin();
                                infsubset != (*backend)->infeasibleSubsets().end(); ++infsubset )
                        {
                            ConditionSet conflict = ConditionSet();
                            for( set<const Formula*>::const_iterator subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                            {
                                for( ConditionVector::const_iterator cond = _state->conditions().begin(); cond != _state->conditions().end(); ++cond )
                                {
                                    if( (*cond)->constraint() == (*subformula)->constraint() )
                                    {
                                        conflict.insert( *cond );
                                        break;
                                    }
                                }
                            }
                            #ifdef SMTRAT_DEVOPTION_Validation
                            if( validationSettings->logTCalls() )
                            {
                                set<const smtrat::Constraint*> constraints = set<const smtrat::Constraint*>();
                                for( ConditionSet::const_iterator cond = conflict.begin(); cond != conflict.end(); ++cond )
                                {
                                    constraints.insert( (**cond).pConstraint() );
                                }
                                smtrat::Module::addAssumptionToCheck( constraints, false, moduleName( (*backend)->type() ) + "_infeasible_subset" );
                            }
                            #endif
                            assert( conflict.size() == infsubset->size() );
                            assert( !conflict.empty() );
                            conflictSet.insert( conflict );
                        }
                        break;
                    }
                }
                assert( !conflictSet.empty() );
                _state->addConflictSet( NULL, conflictSet );
                eraseDTsOfRanking( *_state );

                #ifdef VS_LOG_INTERMEDIATE_STEPS
                logConditions( *_state, false, "Intermediate_conflict_of_VSModule" );
                #endif
                if( _state->isRoot() )
                {
                    /*
                     * If the considered state is the root, update the found infeasible subset as infeasible subset.
                     */
                    updateInfeasibleSubset();
                }
                else
                {
                    /*
                     * If the considered state is not the root, pass the infeasible subset to the father.
                     */
                    _state->passConflictToFather();
                    eraseDTofRanking( _state->rFather() );
                    insertDTinRanking( _state->pFather() );
                }
                return False;
            }
            case Unknown:
            {
                return Unknown;
            }
            default:
            {
                cerr << "Unknown answer type!" << endl;
                assert( false );
                return Unknown;
            }
        }
    }

    #ifdef VS_LOG_INTERMEDIATE_STEPS
    /**
     * Checks the correctness of the symbolic assignment given by the path from the root
     * state to the satisfying state.
     */
    void VSModule::checkAnswer() const
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

    /**
     * Checks whether the set of conditions is is consistent/inconsistent.
     */
    void VSModule::logConditions( const State& _state, bool _assumption, const string& _description ) const
    {
        set<const smtrat::Constraint*> constraints = set<const smtrat::Constraint*>();
        for( ConditionVector::const_iterator cond = _state.conditions().begin(); cond != _state.conditions().end(); ++cond )
        {
            constraints.insert( (**cond).pConstraint() );
        }
        smtrat::Module::addAssumptionToCheck( constraints, _assumption, _description );
    }
    #endif

    /**
     * Prints the history to the output stream.
     *
     * @param _out The output stream where the history should be printed.
     */
    void VSModule::printAll( ostream& _out ) const
    {
        _out << "*** Current solver status, where the constraints" << endl;
        for( FormulaConditionMap::const_iterator cond = mFormulaConditionMap.begin(); cond != mFormulaConditionMap.end(); ++cond )
        {
            _out << "***    ";
            cond->first->print( _out );
            _out << " <-> ";
            cond->second->print( _out );
            _out << endl;
        }
        _out << "*** have been added:" << endl;
        _out << "*** mInconsistentConstraintAdded: " << mInconsistentConstraintAdded << endl;
        _out << "*** mIDCounter: " << mIDCounter << endl;
        printRanking( cout );
        _out << "*** State tree:" << endl;
        mpStateTree->print( "   ", _out );
    }

    /**
     * Prints the history to the output stream.
     *
     * @param _out The output stream where the history should be printed.
     */
    void VSModule::printRanking( ostream& _out ) const
    {
        _out << "*** Current ranking:" << endl;
        for( ValuationMap::const_iterator valDTPair = mRanking.begin(); valDTPair != mRanking.end(); ++valDTPair )
        {
            (*(*valDTPair).second).printAlone( "   ", _out );
        }
    }

    /**
     * Prints the answer if existent.
     *
     * @param _out The output stream where the answer should be printed.
     */
    void VSModule::printAnswer( ostream& _out ) const
    {
        _out << "*** Answer:" << endl;
        if( mRanking.empty() )
        {
            _out << "***        False." << endl;
        }
        else
        {
            _out << "***        True:" << endl;
            const State* currentState = mRanking.begin()->second;
            while( !(*currentState).isRoot() )
            {
                _out << "***           " << (*currentState).substitution().toString2() << endl;
                currentState = (*currentState).pFather();
            }
        }
        _out << endl;
    }
}    // end namespace smtrat

