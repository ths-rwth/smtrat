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

//#define VS_ASSIGNMENT_DEBUG
//#define VS_LOG_INFSUBSETS_OF_BACKEND

namespace smtrat
{
    /**
     * Constructors:
     */

    VSModule::VSModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula )
    {
        mModuleType                      = MT_VSModule;
        #ifdef VS_DEBUG
        debug                            = true;
        #else
        debug                            = false;
        #endif
        #ifdef VS_DEBUG_METHODS
        debugmethods                     = true;
        #else
        debugmethods                     = false;
        #endif
        mInconsistentConstraintAdded     = false;
        mFreshConstraintReceived         = false;
        mIDCounter                       = 0;
        mpStateTree                      = new State();
        mpRanking                        = new ValuationMap();
        mReceivedConstraintsAsConditions = ConstraintConditionMap();
    }

    /**
     * Destructor:
     */
    VSModule::~VSModule()
    {
        while( !mReceivedConstraintsAsConditions.empty() )
        {
            vs::Condition* pRecCond = mReceivedConstraintsAsConditions.begin()->second;
            mReceivedConstraintsAsConditions.erase( mReceivedConstraintsAsConditions.begin() );
            delete pRecCond;
        }
        delete mpRanking;
        delete mpStateTree;
    }

    /**
     * @param _constraint The constraint to add to the already added constraints.
     */
    bool VSModule::assertSubformula( Formula::const_iterator _subformula )
    {
        //cout << __FILE__ << ":" << __func__ << ":" << __LINE__ << endl;
        assert( (*_subformula)->getType() == REALCONSTRAINT );
        Module::assertSubformula( _subformula );
        if( debugmethods )
        {
            cout << __func__ << endl;
        }

        const Constraint* constraint = (*_subformula)->pConstraint();
        vs::Condition*    condition  = new vs::Condition( constraint );
        mReceivedConstraintsAsConditions[constraint] = condition;

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
                mInfeasibleSubsets.back().insert( mpReceivedFormula->back() );
                mInconsistentConstraintAdded = true;
                //cout << __FILE__ << ":" << __func__ << ":" << __LINE__ << endl;
                return false;
            }
            case 1:
            {
                //cout << __FILE__ << ":" << __func__ << ":" << __LINE__ << endl;
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
                mFreshConstraintReceived = true;
                //cout << __FILE__ << ":" << __func__ << ":" << __LINE__ << endl;
                return true;
            }
            default:
            {
                assert( false );
                return true;
            }
        }
    }

    /**
     * Checks the so far received constraints for consistency.
     *
     * @return  True,    if the conjunction of all already added constraints consistent;
     *          False,   if the conjunction of all already added constraints inconsistent;
     *          Unknown, otherwise.
     */
    Answer VSModule::isConsistent()
    {
        //        printReceivedFormula();
        //cout << __FILE__ << ":" << __func__ << ":" << __LINE__ << endl;
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        if( !mFreshConstraintReceived )
        {
            if( mInfeasibleSubsets.empty() )
            {
                return True;
            }
            else
            {
                return False;
            }
        }
        mFreshConstraintReceived = false;
        #ifndef VS_INCREMENTAL
        reset();
        #endif
        if( mpReceivedFormula->empty() )
        {
            return True;
        }
        if( mInconsistentConstraintAdded )
        {
            //cout << __FILE__ << ":" << __func__ << ":" << __LINE__ << endl;
            assert( !mInfeasibleSubsets.empty() );
            assert( !mInfeasibleSubsets.back().empty() );
            return False;
        }

        while( !mpRanking->empty() )
        {
            State* currentState = mpRanking->begin()->second;

            if( currentState->hasChildrenToInsert() )
            {
                currentState->rHasChildrenToInsert() = false;
                insertDTsinRanking( currentState );
            }
            else
            {
                currentState->simplify();
                if( debug )
                {
                    cout << "*** Considered state:" << endl;
                    currentState->printAlone( "   ", cout );
                }
                if( currentState->isInconsistent() )
                {
                    eraseDTsOfRanking( *currentState );
                    if( currentState->isRoot() )
                    {
                        updateInfeasibleSubset();
                    }
                    else
                    {
                        if( currentState->passConflictToFather() )
                        {
                            insertDTinRanking( currentState );
                        }
                        else
                        {
                            eraseDTsOfRanking( currentState->rFather() );
                            insertDTinRanking( currentState->pFather() );
                        }
                    }
                }
                else if( currentState->hasRecentlyAddedConditions() )
                {
                    if( debug )
                    {
                        cout << "*** Propagate new conditions :" << endl;
                    }
                    propagateNewConditions(currentState);
                    if( debug )
                    {
                        cout << "*** Propagate new conditions ready." << endl;
                    }
                }
                else
                {
                    switch( currentState->stateType() )
                    {
                        case SUBSTITUTION_TO_APPLY:
                        {
                            if( debug )
                            {
                                cout << "*** SubstituteAll changes it to:" << endl;
                            }
                            if( !substituteAll( currentState, currentState->rFather().rConditions() ) )
                            {
                                /*
                                 * Delete the currently considered state.
                                 */
                                currentState->rInconsistent() = true;
                                eraseDTofRanking( *currentState );
                            }
                            if( debug )
                            {
                                cout << "*** SubstituteAll ready." << endl;
                            }
                            break;
                        }
                        case COMBINE_SUBRESULTS:
                        {
                            if( debug )
                            {
                                cout << "*** Refresh conditons:" << endl;
                            }
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
                                if( debug )
                                {
                                    currentState->printAlone( "   ", cout );
                                }
                            }
                            else
                            {
                                /*
                                 * If it was the last combination, delete the state.
                                 */
                                currentState->rInconsistent() = true;
                                eraseDTsOfRanking( *currentState );
                            }
                            if( debug )
                            {
                                cout << "*** Conditions refreshed." << endl;
                            }
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
                                    while( !currentState->children().empty() )
                                    {
                                        eraseDTsOfRanking( *currentState->rChildren().back() );
                                        delete currentState->rChildren().back();
                                    }
                                }
                            }

                            /*
                             * Find the most adequate conditions to continue.
                             */
                            vs::Condition * currentCondition;
                            if( !currentState->bestCondition( currentCondition, mAllVariables.size() ) )
                            {
                                /*
                                 * It is a state, where no more elimination could be applied to the conditions.
                                 */
                                if( currentState->conditions().empty() )
                                {
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
                                    }
                                    else
                                    {
                                        /*
                                         * Solution.
                                         */
                                        if( debug )
                                        {
                                            printAll( cout );
                                        }
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
                                            if( !(**child).toHighDegree() &&!(**child).markedAsDeleted() )
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
                                            eraseDTsOfRanking( *currentState );
                                            if( currentState->isRoot() )
                                            {
                                                updateInfeasibleSubset();
                                            }
                                            else
                                            {
                                                if( currentState->passConflictToFather() )
                                                {
                                                    insertDTinRanking( currentState );
                                                }
                                                else
                                                {
                                                    eraseDTsOfRanking( currentState->rFather() );
                                                    insertDTinRanking( currentState->pFather() );
                                                }
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
                                    if( debug )
                                    {
                                        cout << "*** Eliminate " << currentState->index() << " in ";
                                        currentCondition->constraint().print( cout );
                                        cout << " creates:" << endl;
                                    }
                                    if( eliminate( currentState, currentState->index(), currentCondition ) )
                                    {
                                        if( debug )
                                        {
                                            cout << "*** Eliminate ready." << endl;
                                        }
                                    }
                                    else
                                    {
                                        if( debug )
                                        {
                                            cout << "*** No elimination. (Too high degree)" << endl;
                                        }
                                        #ifdef VS_DELAY_BACKEND_CALL
                                        if( (*currentState).toHighDegree() )
                                        {
                                            #endif

                                            /*
                                             * If we need to involve a complete approach.
                                             */
                                            #ifdef VS_WITH_BACKEND
                                            switch( runBackendSolvers( currentState ) )
                                            {
                                                case True:
                                                {
                                                    currentState->rToHighDegree() = true;
                                                    //printAnswer( cout );

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
                                                        if( debug )
                                                        {
                                                            printAll( cout );
                                                        }
                                                        return True;
                                                    }
                                                    break;
                                                }
                                                case False:
                                                {
                                                    currentState->rToHighDegree() = true;
                                                    break;
                                                }
                                                case Unknown:
                                                {
                                                    if( !currentState->rToHighDegree() )
                                                    {
                                                        currentState->rToHighDegree() = true;
                                                        insertDTinRanking( currentState );
                                                        break;
                                                    }
                                                    else
                                                    {
                                                        return Unknown;
                                                    }
                                                }
                                                default:
                                                {
                                                    cout << "Error: Unknown answer in method " << __func__ << " line " << __LINE__ << endl;
                                                    return Unknown;
                                                }
                                            }
                                            #else
                                            currentState->printAlone( "   ", cout );
                                            cout << "###" << endl;
                                            cout << "###                  Unknown!" << endl;
                                            cout << "###" << endl;
                                            mDeductions.clear();
                                            return Unknown;
                                            #endif
                                            #ifdef VS_DELAY_BACKEND_CALL
                                        }
                                        else
                                        {
                                            currentState->rToHighDegree() = true;
                                            insertDTinRanking( currentState );
                                        }
                                        #endif
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
                }
            }
        }
        updateInfeasibleSubset();
        return False;
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void VSModule::removeSubformula( Formula::const_iterator _subformula )
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }

        #ifdef VS_BACKTRACKING
        eraseDTsOfRanking( *mpStateTree );
        ConditionVector condsToDelete  = ConditionVector();
        ConditionVector condsToDeleteB = ConditionVector();
        assert( mpStateTree->hasSubstitutionResults() );
        assert( mpStateTree->substitutionResults().size() == 1 );
        assert( mpStateTree->substitutionResults().back().size() == 1 );
        assert( receivedFormulaSize() == mpStateTree->substitutionResults().back().back().first.size() );
        #endif
        const Constraint* constraint = (*_subformula)->pConstraint();
        vs::Condition*    pCondition = mReceivedConstraintsAsConditions[constraint];
        mReceivedConstraintsAsConditions.erase( constraint );
        delete pCondition;
        Module::removeSubformula( _subformula );
        #ifdef VS_BACKTRACKING
        bool firstConstraintToRemoveFound = false;
        for( ConditionVector::iterator cond = mpStateTree->rSubstitutionResults().back().back().first.begin();
                cond != mpStateTree->rSubstitutionResults().back().back().first.end(); ++cond )
        {
            if( firstConstraintToRemoveFound )
            {
                condsToDeleteB.push_back( *cond );
                mpStateTree->rSubstitutionResults().back().back().first.erase( cond );
            }
            else if( (*cond)->constraint() == **constraintsToRemove.begin() )
            {
                condsToDeleteB.push_back( *cond );
                mpStateTree->rSubstitutionResults().back().back().first.erase( cond );
                firstConstraintToRemoveFound = true;
            }
        }
        assert( firstConstraintToRemoveFound );

        /*
         * Collect the conditions having the conditions to delete as original conditions.
         */
        ConditionVector conditionsToDeleteInRoot = ConditionVector();
        for( ConditionVector::iterator cond = mpStateTree->rConditions().begin(); cond != mpStateTree->conditions().end(); ++cond )
        {
            bool                   originalConditionDeleted = false;
            ConditionSet::iterator oCond                    = (**cond).rOriginalConditions().begin();
            while( oCond != (**cond).originalConditions().end() )
            {
                ConditionVector::const_iterator condToDel = condsToDelete.begin();
                while( condToDel != condsToDelete.end() )
                {
                    if( *oCond == *condToDel )
                    {
                        break;
                    }
                    condToDel++;
                }
                if( condToDel != condsToDelete.end() )
                {
                    (**cond).rOriginalConditions().erase( oCond++ );
                    originalConditionDeleted = true;
                }
                else
                {
                    oCond++;
                }
            }
            if( originalConditionDeleted )
            {
                conditionsToDeleteInRoot.push_back( *cond );
            }
        }

        /*
         * Delete the conditions having only conditions to delete as original conditions.
         */
        mpStateTree->deleteConditions( conditionsToDeleteInRoot );

        while( !condsToDelete.empty() )
        {
            vs::Condition* rpCond = condsToDelete.back();
            condsToDelete.pop_back();
            delete rpCond;
        }

        while( !condsToDeleteB.empty() )
        {
            vs::Condition* rpCond = condsToDeleteB.back();
            condsToDeleteB.pop_back();
            delete rpCond;
        }

        mpStateTree->rTakeSubResultCombAgain() = true;

        insertDTsinRanking( mpStateTree );
        mpStateTree->rTakeSubResultCombAgain() = true;
        #endif

        #ifndef VS_BACKTRACKING
        #ifdef VS_INCREMENTAL
        reset();
        #endif
        #endif

        mFreshConstraintReceived = true;
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
     *              state now is labeled by true, which means, that the constraint
     *              already served to eliminate for the respective variable in this
     *              state.
     */
    bool VSModule::eliminate( State* _currentState, const string& _eliminationVar, vs::Condition* _condition )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << " " << _eliminationVar << " in ";
        (*_condition).constraint().print( cout );
        cout << endl;
        #endif

        /*
         * Get the constraint of this condition.
         */
        const Constraint& constraint = (*_condition).constraint();

        /*
         * Get coefficients of the variable in the constraints.
         */
        symbol sym;
        constraint.variable( _eliminationVar, sym );

        /*
         * Determine the substitution type: normal or +epsilon
         */
        Substitution_Type subType = ST_PLUS_EPSILON;
        if( constraint.relation() == CR_EQ || constraint.relation() == CR_LEQ || constraint.relation() == CR_GEQ )
        {
            subType = ST_NORMAL;
        }

        ex lhs = constraint.lhs();
        if( lhs.degree( ex( sym ) ) > 1 )
        {
            ex derivate            = lhs.diff( sym, 1 );
            ex gcdOfLhsAndDerivate = gcd( lhs, derivate );
            Constraint::normalize( gcdOfLhsAndDerivate );
            if( gcdOfLhsAndDerivate != 1 )
            {
                ex quotient;
                if( gcdOfLhsAndDerivate != 0 && divide( lhs, gcdOfLhsAndDerivate, quotient ) )
                {
                    Constraint::normalize( quotient );
                    lhs = quotient;
                }
            }
        }

        vector<ex> coeffs = vector<ex>();
        for( signed i = 0; i <= lhs.degree( ex( sym ) ); ++i )
        {
            coeffs.push_back( ex( lhs.coeff( ex( sym ), i ) ) );
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
                 * Create state ({b!=0} + oldConditions,
                 *                        [x -> -c/b]):
                 */
                if( (*_currentState).addChild( coeffs.at( 1 ), CR_NEQ,_eliminationVar, -coeffs.at( 0 ), 0, coeffs.at( 1 ), 0, subType, oConditions ) )
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
                    numberOfAddedChildren++;
                    if( debug )
                    {
                        (*(*_currentState).rChildren().back()).print( "   ", cout );
                    }
                }
                break;
            }
            //degree = 2
            case 3:
            {
                ex radicand = ex( pow( coeffs.at( 1 ), 2 ) - 4 * coeffs.at( 2 ) * coeffs.at( 0 ) );
                Constraint::normalize( radicand );

                /*
                 * Create state ({a==0, b!=0} + oldConditions,
                 *                        [x -> -c/b]):
                 */
                if( (*_currentState).addChild( coeffs.at( 2 ), CR_EQ, coeffs.at( 1 ), CR_NEQ, _eliminationVar, -coeffs.at( 0 ), 0, coeffs.at( 1 ), 0, subType, oConditions ) )
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
                    numberOfAddedChildren++;
                    if( debug )
                    {
                        (*(*_currentState).rChildren().back()).print( "   ", cout );
                    }
                }

                /*
                 * Create state ({a!=0, b^2-4ac>=0} + oldConditions,
                 *                        [x -> (-b+sqrt(b^2-4ac))/2a]):
                 */
                if( (*_currentState).addChild( coeffs.at( 2 ), CR_NEQ, radicand, CR_GEQ, _eliminationVar, -coeffs.at( 1 ), 1, 2 * coeffs.at( 2 ), radicand, subType, oConditions ) )
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
                    numberOfAddedChildren++;
                    if( debug )
                    {
                        (*(*_currentState).rChildren().back()).print( "   ", cout );
                    }
                }

                /*
                 * Create state ({a!=0, b^2-4ac>0} + oldConditions,
                 *                        [x -> (-b-sqrt(b^2-4ac))/2a]):
                 */
                if( (*_currentState).addChild( coeffs.at( 2 ), CR_NEQ, radicand, CR_GREATER, _eliminationVar, -coeffs.at( 1 ), -1, 2 * coeffs.at( 2 ), radicand, subType, oConditions ) )
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
                    numberOfAddedChildren++;
                    if( debug )
                    {
                        (*(*_currentState).rChildren().back()).print( "   ", cout );
                    }
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
             * Create state ( Conditions,
             *                [x -> -infinity]):
             */
            if( (*_currentState).addChild( _eliminationVar, ST_MINUS_INFINITY, oConditions ) )
            {
                /*
                 * Add its valuation to the current ranking.
                 */
                insertDTinRanking( (*_currentState).rChildren().back() );
                numberOfAddedChildren++;
                if( debug )
                {
                    (*(*_currentState).rChildren().back()).print( "   ", cout );
                }
            }
        }

        if( generatedTestCandidateBeingASolution )
        {
            for( ConditionVector::iterator cond = _currentState->rConditions().begin(); cond != _currentState->conditions().end(); ++cond )
            {
                (**cond).rFlag() = true;
            }
            assert( numberOfAddedChildren <= _currentState->children().size() );

            while( _currentState->children().size() > numberOfAddedChildren )
            {
                delete *_currentState->rChildren().begin();
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
     * Applies the most recent substitution of _currentState to all conditions in it.
     *
     * @param _currentState     The currently considered state.
     * @param _conditions       The conditions of the state to which the substitution in this
     *                          state shall be applied.
     *
     * @sideeffect: For each case a new brother of the currently considered decision
     *              tuple is generated. The currently considered state gets
     *              deleted.
     */
    bool VSModule::substituteAll( State* _currentState, ConditionVector& _conditions )
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }

        /*
         * Create a vector to store the results of each single substitution. Each entry correponds to
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
                    oldConditions.back()->rOriginalConditions().insert( *cond );
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
                                    currentConjunction.back()->rOriginalConditions().insert( *cond );
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
             * Delete the children of this state.
             */
            while( !_currentState->children().empty() )
            {
                delete _currentState->rChildren().back();
            }

            /*
             * Delete the conflict sets of this state.
             */
            _currentState->rConflictSets().clear();

            /*
             * Delete the conditions of this state.
             */
            while( !_currentState->conditions().empty() )
            {
                vs::Condition* rpCond = _currentState->rConditions().back();
                _currentState->rConditions().pop_back();
                delete rpCond;
            }

            /*
             * Delete the everything in oldConditions.
             */
            while( !oldConditions.empty() )
            {
                vs::Condition* rpCond = oldConditions.back();
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
                        vs::Condition* rpCond = disjunctionsOfCondConj.back().back().back();
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
            if( debug )
            {
                _currentState->print( "   ", cout );
            }
            return true;
        }
    }

    /**
     * Applies the most recent substitutions resp. of each of _currentState to all conditions,
     * which were recently added to _currentState.
     *
     * @param _currentState The currently considered state.
     */
    void VSModule::propagateNewConditions( State* _currentState )
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        eraseDTsOfRanking( *_currentState );
        _currentState->rHasRecentlyAddedConditions() = false;

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
                while( !_currentState->children().empty() )
                {
                    delete _currentState->rChildren().back();
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
                                            if( debug )
                                            {
                                                cout << "*** Eliminate " << _currentState->index() << " in ";
                                                (**cond).constraint().print( cout );
                                                cout << " creates:" << endl;
                                            }
                                            eliminate( _currentState, _currentState->index(), *cond );
                                            if( debug )
                                            {
                                                cout << "*** Eliminate ready." << endl;
                                            }
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
     * Increases the ID to allocate.
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
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        if( !_state->markedAsDeleted() &&!(_state->isInconsistent() && _state->conflictSets().empty() && _state->conditionsSimplified()) )
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

            if( (mpRanking->insert( ValStatePair( _state->valuationPlusID(), _state ) )).second == false )
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
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        insertDTinRanking( _state );

        if( _state->conditionsSimplified() && _state->subResultsSimplified() )
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
     * @param _state The states, which will be deleted.
     *
     * @return  True, if the state was in the ranking.
     */
    bool VSModule::eraseDTofRanking( State& _state )
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        ValuationMap::iterator valDTPair = (*mpRanking).find( _state.valuationPlusID() );
        if( valDTPair != (*mpRanking).end() )
        {
            (*mpRanking).erase( valDTPair );
            _state.setID( 0 );
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * Erases a state and its sucessors of the ranking.
     *
     * @param _state The root of the states, which will be deleted.
     */
    void VSModule::eraseDTsOfRanking( State& _state )
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        eraseDTofRanking( _state );

        for( StateVector::iterator dt = _state.rChildren().begin(); dt != _state.children().end(); ++dt )
        {
            eraseDTsOfRanking( **dt );
        }
    }

    /**
     * Update the infeasible subset. It is not empty, if the set of received constraints is inconsistent.
     */
    void VSModule::updateInfeasibleSubset()
    {
        //cout << __FILE__ << ":" << __func__ << ":" << __LINE__ << endl;
        if( debugmethods )
        {
            cout << __FILE__ << ":" << __func__ << ":" << __LINE__ << endl;
        }
        #ifdef VS_INFEASIBLE_SUBSET_GENERATION

        /*
         * Determine the minimum covering sets of the conflict sets, i.e. the infeasible subsets
         * of the root.
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
        assert( !minCoverSets.empty() );

        /*
         * Change the globally stored infeasible subset to the smaller one.
         */
        mInfeasibleSubsets.clear();
        mInfeasibleSubsets.push_back( set<const Formula*>() );
        for( ConditionSetSet::const_iterator minCoverSet = minCoverSets.begin(); minCoverSet != minCoverSets.end(); ++minCoverSet )
        {
            assert( !minCoverSet->empty() );
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

                    if( receivedConstraint == mpReceivedFormula->end() )
                    {
                        cout << "BLA1" << endl;
                        printAll( cout );
                        assert( false );
                    }

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
     * Resets everything in the solver except of the received constraints and the backtrack point history.
     */
    void VSModule::reset()
    {
        //cout << __FILE__ << ":" << __func__ << ":" << __LINE__ << endl;
        if( debugmethods )
        {
            cout << __func__ << endl;
        }

        /*
         * Delete everything but the received constraints and their variables including
         * the variable valuations.
         */
        delete mpRanking;
        delete mpStateTree;

        /*
         * Initialize everything but the received constraints and their variablesincluding
         * the variable valuations.
         */
        mInconsistentConstraintAdded = false;
        mIDCounter                   = 0;
        mInfeasibleSubsets.clear();
        mpStateTree = new State();
        mpRanking   = new ValuationMap();

        while( !mReceivedConstraintsAsConditions.empty() )
        {
            vs::Condition* pRecCond = mReceivedConstraintsAsConditions.begin()->second;
            mReceivedConstraintsAsConditions.erase( mReceivedConstraintsAsConditions.begin() );
            delete pRecCond;
        }

        Formula::const_iterator cons = mpReceivedFormula->begin();
        while( cons != mpReceivedFormula->end() )
        {
            vs::Condition* condition = new vs::Condition( (*cons)->pConstraint() );
            mReceivedConstraintsAsConditions[(*cons)->pConstraint()] = condition;

            /*
             * Check the consistency of the constraint to add.
             */
            unsigned isConstraintConsistent = (*cons)->constraint().isConsistent();

            /*
             * Clear the ranking.
             */
            if( isConstraintConsistent != 1 )
            {
                eraseDTsOfRanking( *mpStateTree );
                mIDCounter = 0;

                /*
                 * Add the variables of the new constraint to the history of all occured variables.
                 */
                if( isConstraintConsistent == 2 )
                {
                    //              mpStateTree->rConditions().push_back( new Condition( *cons, 0 ) );
                    //              (*(mpStateTree->rConditions()).back()).rRecentlyAdded() = true;
                    //              mpStateTree->rConditions().back()->rOriginalConditions().insert( cond->second );

                    ConditionSet oConds = ConditionSet();
                    oConds.insert( condition );

                    vector<DisjunctionOfConditionConjunctions> subResults = vector<DisjunctionOfConditionConjunctions>();
                    DisjunctionOfConditionConjunctions subResult = DisjunctionOfConditionConjunctions();
                    ConditionVector condVector                   = ConditionVector();
                    condVector.push_back( new vs::Condition( (*cons)->pConstraint(), false, oConds, 0 ) );
                    subResult.push_back( condVector );
                    subResults.push_back( subResult );
                    mpStateTree->addSubstitutionResults( subResults );

                    mpStateTree->rHasRecentlyAddedConditions() = true;
                    insertDTinRanking( mpStateTree );
                }
                else if( isConstraintConsistent == 0 )
                {
                    //cout << __FILE__ << ":" << __func__ << ":" << __LINE__ << endl;
                    mInfeasibleSubsets.push_back( set<const Formula*>() );
                    mInfeasibleSubsets.back().insert( *cons );
                    mInconsistentConstraintAdded = true;
                }
            }
            cons++;
        }
    }

    #ifdef VS_USE_DEDUCTIONS

    /**
     * Updates the deductions.
     */
    void VSModule::updateDeductions()
    {
        if( !mFreshConstraintReceived )
        {
            mDeductions.clear();
            if( mInfeasibleSubsets.empty() )
            {
                vector<pair<string, numeric> > assignment = getNumericAssignment();
                lst substitutionList = lst();
                for( vector<pair<string, numeric> >::const_iterator assign = assignment.begin(); assign != assignment.end(); ++assign )
                {
                    substitutionList.append( mAllVariables[assign->first] == assign->second );
                }
                for( fcs_const_iterator constraint = mConstraintsToInform.begin(); constraint != mConstraintsToInform.end(); ++constraint )
                {
                    ex tmpLhs                = (*constraint)->lhs().subs( substitutionList );
                    Constraint tmpConstraint = Constraint( tmpLhs, (*constraint)->relation(), (*constraint)->variables() );
                    if( tmpConstraint.isConsistent() == 1 )
                    {
                        mDeductions.push_back( *constraint );
                    }
                }
            }
        }
    }
    #endif

    /**
     * Gets a symbolic assignment, if an assignment exists and the consistency check determined
     * the satisfiability of the given set of constraints.
     *
     * @return A symbolic assignment.
     */
    vector<pair<string, pair<Substitution_Type, ex> > > VSModule::getSymbolicAssignment() const
    {
        assert( !mFreshConstraintReceived && mInfeasibleSubsets.empty() );
        vector<pair<string, pair<Substitution_Type, ex> > > result    = vector<pair<string, pair<Substitution_Type, ex> > >();
        vector<pair<string, pair<Substitution_Type, ex> > > resultTmp = vector<pair<string, pair<Substitution_Type, ex> > >();
        symtab uncheckedVariables = mAllVariables;
        const State* currentState = mpRanking->begin()->second;
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

    #ifdef VS_USE_DEDUCTIONS

    /**
     * Gets a numeric assignment, if an assignment exists and the consistency check determined
     * the satisfiability of the given set of constraints.
     *
     * @return A numeric assignment.
     */
    vector<pair<string, numeric> > VSModule::getNumericAssignment( const unsigned _refinementParameter ) const
    {
        #ifdef VS_ASSIGNMENT_DEBUG
        cout << __func__ << "(" << _refinementParameter << ") :" << __LINE__ << endl;
        #endif
        assert( !mFreshConstraintReceived && mInfeasibleSubsets.empty() );
        vector<pair<string, numeric> > result       = vector<pair<string, numeric> >();
        vector<pair<string, ex> >      resultTmp    = vector<pair<string, ex> >();
        vector<Constraint>             constraintsA = vector<Constraint>();
        for( Formula::const_iterator subformula = receivedFormulaBegin(); subformula != receivedFormulaEnd(); ++subformula )
        {
            constraintsA.push_back( (*subformula)->constraint() );
        }
        vector<pair<string, pair<Substitution_Type, ex> > > symbolicAssignment = getSymbolicAssignment();
        unsigned                                            counter            = 0;
        symtab vars = mAllVariables;
        for( vector<pair<string, pair<Substitution_Type, ex> > >::iterator symAssign = symbolicAssignment.begin();
                symAssign != symbolicAssignment.end(); ++symAssign )
        {
            #ifdef VS_ASSIGNMENT_DEBUG
            cout << "constraints: " << endl;
            for( vector<Constraint>::const_iterator cons = constraintsA.begin(); cons != constraintsA.end(); ++cons )
            {
                cout << "    " << cons->toString() << endl;
            }
            cout << "symAssign: " << endl;
            for( vector<pair<string, pair<Substitution_Type, ex> > >::const_iterator iter = symbolicAssignment.begin();
                    iter != symbolicAssignment.end(); ++iter )
            {
                cout << "    " << iter->first << "  ->  ( " << iter->second.first << " , " << iter->second.second << " )" << endl;
            }
            #endif
            //            assert( is_a<numeric>( symAssign->second.second ) );

            Substitution_Type currentSubsType = symAssign->second.first;
            string currentVarName             = symAssign->first;
            symtab::const_iterator var = mAllVariables.find( symAssign->first );
            assert( var != mAllVariables.end() );
            const ex currentVar = var->second;
            ex currentAssignValue = symAssign->second.second;
            if( currentSubsType == ST_PLUS_EPSILON )
            {
                std::stringstream out;
                out << "eps_" << counter++;
                symbol eps( out.str() );
                currentAssignValue += eps;
                vars[out.str()]    = eps;
            }
            else if( currentSubsType == ST_MINUS_INFINITY )
            {
                std::stringstream out;
                out << "inf_" << counter++;
                symbol inf( out.str() );
                currentAssignValue -= inf;
                vars[out.str()]    = inf;
            }

            resultTmp.push_back( pair<string, ex>( currentVarName, currentAssignValue ) );
            pair<string, ex>& numAssign = resultTmp.back();
            #ifdef VS_ASSIGNMENT_DEBUG
            cout << numAssign.first << "  ->  " << numAssign.second << endl;
            #endif

            vector<Constraint>                 tmpConstraints = vector<Constraint>();
            vector<Constraint>::const_iterator constraint     = constraintsA.begin();
            while( constraint != constraintsA.end() )
            {
                ex tmpLhs                = constraint->lhs().subs( currentVar == numAssign.second );
                Constraint tmpConstraint = Constraint( tmpLhs, constraint->relation(), vars );
                unsigned consistent = tmpConstraint.isConsistent();
                assert( consistent != 0 );
                if( consistent == 2 )
                {
                    tmpConstraints.push_back( tmpConstraint );
                }
                ++constraint;
            }
            constraintsA.clear();
            constraintsA.insert( constraintsA.end(), tmpConstraints.begin(), tmpConstraints.end() );

            for( vector<pair<string, pair<Substitution_Type, ex> > >::iterator symAssignTmp = symAssign; symAssignTmp != symbolicAssignment.end();
                    ++symAssignTmp )
            {
                symAssignTmp->second.second = symAssignTmp->second.second.subs( currentVar == numAssign.second );
            }
        }
        #ifdef VS_ASSIGNMENT_DEBUG
        cout << __func__ << ":" << __LINE__ << endl;
        #endif
        return result;
    }
    #endif

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
     * Adapts the passed formula according to the current assignment within the SAT solver.
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
            addSubformulaToPassedFormula( new smtrat::Formula( smtrat::Formula::newConstraint( iter->lhs(), iter->relation() ) ), origins );
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
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif

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
                    if( !(*backend)->rInfeasibleSubsets().empty() )
                    {
                        for( vec_set_const_pFormula::const_iterator infsubset = (*backend)->rInfeasibleSubsets().begin();
                                infsubset != (*backend)->rInfeasibleSubsets().end(); ++infsubset )
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

                            #ifdef VS_LOG_INFSUBSETS_OF_BACKEND
                            set< const smtrat::Constraint* > constraints = set< const smtrat::Constraint* >();
                            for( ConditionSet::const_iterator cond = conflict.begin(); cond != conflict.end(); ++cond )
                            {
                                constraints.insert( (**cond).pConstraint() );
                            }
                            smtrat::Module::addAssumptionToCheck( constraints, false, "IS_of_Backend_of_VSModule" );
                            #endif
//                            if( conflict.size() != infsubset->size() )
//                            {
//                                cout << "infeasible subset = {";
//                                for( set<const Formula*>::const_iterator subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
//                                {
//                                    cout << " " << (*subformula)->constraint();
//                                }
//                                cout << " }" << endl;
//                                cout << "projected infeasible subset = {";
//                                for( ConditionSet::const_iterator cond = conflict.begin(); cond != conflict.end(); ++cond )
//                                {
//                                    cout << " " << (*cond)->constraint();
//                                }
//                                cout << " }" << endl;
//                                (*backend)->print();
//                                _state->printAlone();
//                                assert( false );
//                            }
                            assert( conflict.size() == infsubset->size() ); // If this assertion fails, uncomment the code above
                            if( conflict.empty() )
                            {
                                _state->printAlone( "", cout );
                                print();
                                (*backend)->print();
                            }
                            assert( !conflict.empty() );
                            conflictSet.insert( conflict );
                        }
                        break;
                    }
                }
                _state->addConflictSet( NULL, conflictSet );

                eraseDTsOfRanking( *_state );

                /*
                * If the considered state is the root, update the found infeasible subset as infeasible subset.
                */
                if( _state->isRoot() )
                {
                    updateInfeasibleSubset();
                }

                /*
                * If the considered state is not the root, pass the infeasible subset to the father.
                */
                else
                {
                    if( _state->passConflictToFather() )
                    {
                        insertDTinRanking( _state );
                    }
                    else
                    {
                        eraseDTsOfRanking( _state->rFather() );
                        insertDTinRanking( _state->pFather() );
                    }
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

    vec_set_const_pFormula VSModule::getOriginsOfCondition( const vs::Condition* _condition, const vs::State* _state ) const
    {
        vec_set_const_pFormula result = vec_set_const_pFormula();
        set<const vs::Condition*> currentOrigins = set<const vs::Condition*>();
        currentOrigins.insert( _condition );
        set<const vs::Condition*> currentOriginsOrigins = set<const vs::Condition*>();
        const State*              currentState          = _state;
        while( !currentState->isRoot() )
        {
            currentOriginsOrigins.clear();
            for( set<const vs::Condition*>::iterator ocond = currentOrigins.begin(); ocond != currentOrigins.end(); ++ocond )
            {
                if( (*ocond)->originalConditions().empty() )
                {
                    currentOriginsOrigins.insert( currentState->pOriginalCondition() );
                }
                else
                {
                    currentOriginsOrigins.insert( (*ocond)->originalConditions().begin(), (*ocond)->originalConditions().end() );
                }
            }
            currentOrigins = currentOriginsOrigins;
            currentState   = currentState->pFather();
        }

        return result;
    }

    /**
     * Prints the history to the output stream.
     *
     * @param _out The output stream where the history should be printed.
     */
    void VSModule::printAll( ostream& _out ) const
    {
        _out << "*** Current solver status, where the constraints" << endl;
        for( ConstraintConditionMap::const_iterator cond = mReceivedConstraintsAsConditions.begin(); cond != mReceivedConstraintsAsConditions.end();
                ++cond )
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
        unsigned counter = 0;
        for( ValuationMap::const_iterator valDTPair = (*mpRanking).begin(); valDTPair != (*mpRanking).end(); ++valDTPair )
        {
            counter++;
            (*(*valDTPair).second).printAlone( "   ", _out );
            if( counter > 10 )
            {
                break;
            }
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
        if( (*mpRanking).empty() )
        {
            _out << "***        False." << endl;
        }
        else
        {
            _out << "***        True:" << endl;
            const State* currentState = (*(*mpRanking).begin()).second;
            while( !(*currentState).isRoot() )
            {
                _out << "***           " << (*currentState).substitution().toString2() << endl;
                currentState = (*currentState).pFather();
            }
        }
        _out << endl;
    }

}    // end namespace smtrat

