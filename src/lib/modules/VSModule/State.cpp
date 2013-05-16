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


/**
 * Class to create a state object.
 * @author Florian Corzilius
 * @since 2010-05-11
 * @version 2011-12-05
 */

#include <cmath>
#include <float.h>

#include "State.h"
#include "../../Module.h"

//#define VS_DEBUG_METHODS
//#define VS_DEBUG_METHODS_X
//#define VS_DEBUG_BACKENDS
//#define VS_DEBUG_BACKENDS_EXTENDED
//#define VS_LOG_INFSUBSETS

namespace vs
{
    using namespace std;
    using namespace GiNaC;
    #ifdef SMTRAT_VS_VARIABLEBOUNDS
    using namespace GiNaCRA;
    #endif

    /**
     * Constructors:
     */
    State::State():
        mConditionsSimplified( false ),
        mHasChildrenToInsert( false ),
        mHasRecentlyAddedConditions( false ),
        mInconsistent( false ),
        mMarkedAsDeleted( false ),
        mSubResultsSimplified( false ),
        mTakeSubResultCombAgain( false ),
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        mTestCandidateCheckedForBounds( false ),
        mTestCandidateInBoundsCreated( false ),
        #endif
        mToHighDegree( false ),
        mTryToRefreshIndex( false ),
        mID( 0 ),
        mValuation( 0 ),
        mStateType( TEST_CANDIDATE_TO_GENERATE ),
        mpIndex( new string( "" ) ),
        mpOriginalCondition( NULL ),
        mpFather( NULL ),
        mpSubstitution( NULL ),
        mpSubstitutionResults( NULL ),
        mpSubResultCombination( NULL ),
        mpConditions( new ConditionVector() ),
        mpConflictSets( new ConflictSets() ),
        mpChildren( new StateVector() )
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        ,
        mpVariableBounds( new VariableBounds() )
        #endif
    {
    }

    State::State( State* const _father, const Substitution& _substitution ):
        mConditionsSimplified( false ),
        mHasChildrenToInsert( false ),
        mHasRecentlyAddedConditions( false ),
        mInconsistent( false ),
        mMarkedAsDeleted( false ),
        mSubResultsSimplified( false ),
        mTakeSubResultCombAgain( false ),
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        mTestCandidateCheckedForBounds( false ),
        mTestCandidateInBoundsCreated( false ),
        #endif
        mToHighDegree( false ),
        mTryToRefreshIndex( false ),
        mID( 0 ),
        mValuation( 0 ),
        mStateType( SUBSTITUTION_TO_APPLY ),
        mpIndex( new string( "" ) ),
        mpOriginalCondition( NULL ),
        mpFather( _father ),
        mpSubstitution( new Substitution( _substitution ) ),
        mpSubstitutionResults( NULL ),
        mpSubResultCombination( NULL ),
        mpConditions( new ConditionVector() ),
        mpConflictSets( new ConflictSets() ),
        mpChildren( new StateVector() )
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        ,
        mpVariableBounds( new VariableBounds() )
        #endif
    {
    }

    /**
     * Destructor:
     */
    State::~State()
    {
        delete mpConflictSets;
        while( !children().empty() )
        {
            State* rpChild = rChildren().back();
            rChildren().pop_back();
            delete rpChild;
        }
        delete mpChildren;
        while( !conditions().empty() )
        {
            const Condition* pCond = rConditions().back();
            rConditions().pop_back();
            #ifdef SMTRAT_VS_VARIABLEBOUNDS
            mpVariableBounds->removeBound( pCond->pConstraint(), pCond );
            #endif
            delete pCond;
        }
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        delete mpVariableBounds;
        #endif
        delete mpConditions;
        if( mpSubstitution != NULL ) delete mpSubstitution;
        delete mpIndex;
        if( mpSubstitutionResults != NULL )
        {
            while( !mpSubstitutionResults->empty() )
            {
                while( !mpSubstitutionResults->back().empty() )
                {
                    while( !mpSubstitutionResults->back().back().first.empty() )
                    {
                        const Condition* rpCond = mpSubstitutionResults->back().back().first.back();
                        mpSubstitutionResults->back().back().first.pop_back();
                        delete rpCond;
                    }
                    mpSubstitutionResults->back().pop_back();
                }
                mpSubstitutionResults->pop_back();
            }
            delete mpSubstitutionResults;
            delete mpSubResultCombination;
        }
    }

    /**
     * Methods:
     */

    /**
     * @return The depth of the subtree with this state as root node.
     */
    unsigned State::treeDepth() const
    {
        unsigned     depth     = 0;
        const State* currentDT = this;
        while( !(*currentDT).isRoot() )
        {
            ++depth;
            currentDT = (*currentDT).pFather();
        }
        return depth;
    }

    /**
     * Checks if a substitution can be applied.
     *
     * @return  True,   if a substitution can be applied.
     *          False,  else.
     */
    bool State::substitutionApplicable() const
    {
        ConditionVector::const_iterator cond = conditions().begin();
        while( cond != conditions().end() )
        {
            if( substitutionApplicable( (**cond).constraint() ) )
            {
                return true;
            }
            ++cond;
        }
        return false;
    }

    /**
     * Checks if the substitution of this state can be applied to the given
     * constraint.
     *
     * @param _constraint   The constraint, for which we want to know, if the substitution
     *                      is appliable.
     *
     * @return  True,   if the substitution can be applied.
     *          False,  else.
     */
    bool State::substitutionApplicable( const smtrat::Constraint& _constraint ) const
    {
        if( !isRoot() )
        {
            if( _constraint.variables().find( substitution().variable() ) != _constraint.variables().end() )
            {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks whether a condition exists, which was not involved in an elimination step.
     *
     * @return True, if there exists a condition in the state, which was
     *         not already involved in an elimination step.
     */
    bool State::hasNoninvolvedCondition() const
    {
        ConditionVector::const_iterator cond = conditions().begin();
        while( cond != conditions().end() )
        {
            if( (*cond)->flag() )
                ++cond;
            else
                return true;
        }
        return false;
    }

    /**
     * Checks whether a child exists, which has no ID (!=0).
     *
     * @return True, if there exists a child with ID (!=0).
     */
    bool State::hasChildWithID() const
    {
        StateVector::const_iterator child = children().begin();
        while( child != children().end() )
        {
            if( (*child)->id() == 0 )
                ++child;
            else
                return true;
        }
        return false;
    }

    /**
     * Checks whether the given variable occurs in a equation.
     *
     * @return  true,   if the given variable occurs in a equation;
     *          false,  otherwise.
     */
    bool State::occursInEquation( const string& _variableName ) const
    {
        for( ConditionVector::const_iterator cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            if( (*cond)->constraint().relation() == smtrat::CR_EQ && (*cond)->constraint().hasVariable( _variableName ) )
            {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks whether there exist more than one test candidate, which has still not been checked.
     *
     * @return  true,   if there exist more than one test candidate, which has still not been checked;
     *          false,  otherwise.
     */
    bool State::hasFurtherUncheckedTestCandidates() const
    {
        if( children().size() > 1 )
        {
            return true;
        }
        else
        {
            for( ConditionVector::const_iterator cond = conditions().begin(); cond != conditions().end(); ++cond )
            {
                if( !(**cond).flag() )
                    return true;
            }
            return false;
        }
    }

    /**
     * Finds the variables, which occur in this decision triple.
     *
     * @param _variables The variables which occur in this decision triple.
     */
    void State::variables( set<string>& _variables ) const
    {
        for( ConditionVector::const_iterator cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            for( symtab::const_iterator var = (**cond).constraint().variables().begin(); var != (**cond).constraint().variables().end(); ++var )
            {
                _variables.insert( (*var).first );
            }
        }
    }

    /**
     * Determines the number of nodes in the tree with this state as root.
     *
     * @return The number of nodes in the tree with this state as root.
     */
    unsigned State::numberOfNodes() const
    {
        unsigned result = 1;
        for( StateVector::const_iterator child = children().begin(); child != children().end(); ++child )
        {
            result += (**child).numberOfNodes();
        }
        return result;
    }

    /**
     * The sum of the ID and the valuation times the valuation factor.
     *
     * @return The sum of the ID and the valuation times the valuation factor.
     */
    const pair<unsigned, unsigned> State::valuationPlusID() const
    {
        return pair<unsigned, unsigned>( valuation(), id() );
    }

    /**
     * Checks the substitution result combination vector.
     *
     * @return  true,   if there is an error in the substitution result combination vector;
     *          false,  otherwise.
     */
    bool State::checkSubResultsCombs() const
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif
        if( hasSubstitutionResults() )
        {
            if( hasSubResultsCombination() )
            {
                for( SubResultCombination::const_iterator subResComb = subResultCombination().begin(); subResComb != subResultCombination().end();
                        ++subResComb )
                {
                    if( subResComb->first < 0 || subResComb->first >= substitutionResults().size() )
                    {
                        return true;
                    }
                    else
                    {
                        if( subResComb->second < 0 || subResComb->second >= mpSubstitutionResults->at( subResComb->first ).size()
                                || mpSubstitutionResults->at( subResComb->first ).size() == 0 )
                        {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    /**
     * @return The root of the tree, in which this state is located.
     */
    State& State::root()
    {
        State* currentDT = this;
        while( !(*currentDT).isRoot() )
        {
            currentDT = (*currentDT).pFather();
        }
        return *currentDT;
    }

    /**
     * Determines (if it exists) a ancestor node, which is unfinished, that is
     * it has still substitution results to consider.
     *
     * @param _unfinAnt The unfinished ancestor node.
     *
     * @return  true,   if it has a unfinished ancestor;
     *          false,  otherwise.
     */
    bool State::unfinishedAncestor( State*& _unfinAnt )
    {
        #ifdef VS_DEBUG_METHODS_X
        cout << __func__ << endl;
        #endif
        _unfinAnt = this;
        while( !_unfinAnt->isRoot() )
        {
            if( _unfinAnt->unfinished() )
            {
                return true;
            }
            _unfinAnt = _unfinAnt->pFather();
        }
        return false;
    }

    /**
     * Determines the most adequate condition and in it the most adequate variable in
     * the state to generate test candidates for.
     *
     * @param _bestCondition        The most adequate condition to be the next test candidate provider.
     * @param _numberOfAllVariables The number of all globally known variables.
     *
     * @return true     ,if it has a condition and a variable in it to generate test candidates for;
     *         false    ,otherwise.
     */
    bool State::bestCondition( const Condition*& _bestCondition, const unsigned _numberOfAllVariables )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif
        ConditionVector::iterator cond = rConditions().begin();
        if( cond == conditions().end() )
        {
            return false;
        }
        else
        {
            assert( index() != "" );
            /*
             * Find the best condition.
             */
            _bestCondition = *cond;
            ++cond;
            double bestConditionValuation    = _bestCondition->valuate( index(), _numberOfAllVariables, true );
            double currentConditionValuation = 0;
            while( cond != conditions().end() )
            {
                if( !(**cond).flag() )
                {
                    if( (*_bestCondition).flag() )
                    {
                        _bestCondition         = *cond;
                        bestConditionValuation = _bestCondition->valuate( index(), _numberOfAllVariables, true );
                    }
                    else
                    {
                        currentConditionValuation = (**cond).valuate( index(), _numberOfAllVariables, true );
                        if( currentConditionValuation != 0 && ( currentConditionValuation < bestConditionValuation || bestConditionValuation == 0 ) )
                        {
                            _bestCondition         = *cond;
                            bestConditionValuation = currentConditionValuation;
                        }
                    }
                }
                ++cond;
            }
            /*
             * If all constraints were considered to yield test candidates, return false
             * which means that there is no condition in general. Otherwise return true.
             */
            return !(*_bestCondition).flag();
        }
    }

    /**
     * Checks if the given constraint already exists as condition in the state.
     *
     * @param _constraint   The constraint, for which we want to know, if it already
     *                      exists as condition in the state.
     *
     * @return An iterator to the condition, which involves the constraint or an iterator
     *         to the end of the vector of conditions of this state.
     */
    ConditionVector::iterator State::constraintExists( const smtrat::Constraint& _constraint )
    {
        for( ConditionVector::iterator cond = rConditions().begin(); cond != conditions().end(); ++cond )
        {
            if( (**cond).constraint() == _constraint )
            {
                return cond;
            }
        }
        return rConditions().end();
    }

    /**
     * Cleans up all conditions in this state according to comparison between the corresponding constraints.
     */
    void State::simplify()
    {
        #ifdef VS_DEBUG_METHODS_X
        cout << __func__ << endl;
        #endif
        #ifdef VS_DEBUG_BACKENDS
        printAlone( "", cout );
        #endif

        if( !subResultsSimplified() )
        {
            if( hasSubstitutionResults() )
            {
                /*
                 * If these conjunction together are consistent, simplify all conjunctions of
                 * conditions in the remaining substitution results being disjunctions.
                 */
                unsigned                      subResultIndex  = 0;
                SubstitutionResults::iterator subResult       = mpSubstitutionResults->begin();
                SubstitutionResults::iterator fixedConditions = mpSubstitutionResults->end();
                while( subResult != mpSubstitutionResults->end() )
                {
                    assert( !subResult->empty() );
                    SubstitutionResult::iterator condConjunction = subResult->begin();
                    bool containsEmptyCase = false;
                    while( condConjunction != subResult->end() && subResult->size() > 1 )
                    {
                        ConditionVector redundantConditions       = ConditionVector();
                        ConditionSetSet conflictingConditionPairs = ConditionSetSet();
                        if( !simplify( condConjunction->first, redundantConditions, conflictingConditionPairs ) )
                        {
                            while( !condConjunction->first.empty() )
                            {
                                const Condition* rpCond = condConjunction->first.back();
                                condConjunction->first.pop_back();
                                delete rpCond;
                            }
                            condConjunction = subResult->erase( condConjunction );
                        }
                        else
                        {
                            if( condConjunction->first.empty() ) containsEmptyCase = true;
                            ++condConjunction;
                        }
                        while( !redundantConditions.empty() )
                        {
                            const Condition* toDelete = redundantConditions.back();
                            redundantConditions.pop_back();
                            delete toDelete;
                        }
                    }
                    if( containsEmptyCase )
                    {
                        if( hasSubResultsCombination() )
                        {
                            SubResultCombination::iterator subResComb = rSubResultCombination().begin();
                            while( subResComb != subResultCombination().end() )
                            {
                                if( subResComb->first == subResultIndex )
                                {
                                    subResComb = rSubResultCombination().erase( subResComb );
                                }
                                else if( subResComb->first > subResultIndex )
                                {
                                    --(subResComb->first);
                                    ++subResComb;
                                }
                                else
                                {
                                    ++subResComb;
                                }
                            }
                        }
                        bool fixedPosWasEndBefore = (fixedConditions == mpSubstitutionResults->end());
                        while( !subResult->empty() )
                        {
                            while( !subResult->back().first.empty() )
                            {
                                const Condition* rpCond = subResult->back().first.back();
                                subResult->back().first.pop_back();
                                delete rpCond;
                            }
                            subResult->pop_back();
                        }
                        subResult = mpSubstitutionResults->erase( subResult );
                        if( fixedPosWasEndBefore ) fixedConditions = mpSubstitutionResults->end();
                        if( mpSubResultCombination != NULL )
                        {
                            if( mpSubResultCombination->size() > 0 )
                            {
                                mTakeSubResultCombAgain = true;
                            }
                            assert( mpSubResultCombination->size() <= mpSubstitutionResults->size() );
                        }
                    }
                    else
                    {
                        if( subResult->size() == 1 )
                        {
                            if( fixedConditions == mpSubstitutionResults->end() )
                            {
                                fixedConditions = subResult;
                                ++subResult;
                                ++subResultIndex;
                            }
                            else
                            {
                                fixedConditions->back().first.insert( fixedConditions->back().first.end(),
                                                                    subResult->back().first.begin(),
                                                                    subResult->back().first.end() );
                                if( hasSubResultsCombination() )
                                {
                                    SubResultCombination::iterator subResComb = rSubResultCombination().begin();
                                    while( subResComb != subResultCombination().end() )
                                    {
                                        if( subResComb->first == subResultIndex )
                                        {
                                            subResComb = rSubResultCombination().erase( subResComb );
                                        }
                                        else if( subResComb->first > subResultIndex )
                                        {
                                            --(subResComb->first);
                                            ++subResComb;
                                        }
                                        else
                                        {
                                            ++subResComb;
                                        }
                                    }
                                }
                                subResult = mpSubstitutionResults->erase( subResult );
                                if( mpSubResultCombination != NULL )
                                {
                                    if( mpSubResultCombination->size() > 0 )
                                    {
                                        mTakeSubResultCombAgain = true;
                                    }
                                    assert( mpSubResultCombination->size() <= mpSubstitutionResults->size() );
                                }
                            }
                        }
                        else
                        {
                            ++subResult;
                            ++subResultIndex;
                        }
                    }
                }

                /*
                 * If the state is already inconsistent update obvious conflicts.
                 */
                if( isInconsistent() && fixedConditions != mpSubstitutionResults->end() )
                {
                    ConditionVector redundantConditions       = ConditionVector();
                    ConditionSetSet conflictingConditionPairs = ConditionSetSet();
                    if( !simplify( fixedConditions->back().first, redundantConditions, conflictingConditionPairs ) )
                    {
                        addConflicts( NULL, conflictingConditionPairs );
//                        if( !isRoot() ) passConflictToFather();
                    }
                    while( !redundantConditions.empty() )
                    {
                        const Condition* toDelete = redundantConditions.back();
                        redundantConditions.pop_back();
                        delete toDelete;
                    }
                }
            }
            mSubResultsSimplified = true;
        }
        /*
         * Simplify the condition vector.
         */
        if( !conditionsSimplified() )
        {
            ConditionVector redundantConditions       = ConditionVector();
            ConditionSetSet conflictingConditionPairs = ConditionSetSet();
            if( !simplify( rConditions(), redundantConditions, conflictingConditionPairs ) )
            {
                addConflictSet( NULL, conflictingConditionPairs );
                rInconsistent() = true;
            }
            else
            {
                deleteConditions( redundantConditions );
            }
            while( !redundantConditions.empty() )
            {
                const Condition* toDelete = redundantConditions.back();
                redundantConditions.pop_back();
                delete toDelete;
            }
            mConditionsSimplified = true;
        }
        #ifdef VS_DEBUG_METHODS_X
        cout << "end " << __func__ << "1" << endl;
        #endif
    }

    /**
     * Simplifies the given conditions according to comparison between the corresponding constraints.
     *
     * @param _conditionVectorToSimplify    The conditions to simplify. Note, that this method can change these conditions.
     * @param _deletedConditions            The conditions which are redundant.
     * @param _conflictSet                  The conflicting pairs of conditions.
     *
     * @return  true,   if the conditions are not obviously conflicting;
     *          false,  otherwise.
     */
    bool State::simplify( ConditionVector& _conditionVectorToSimplify, ConditionVector& _redundantConditions, ConditionSetSet& _conflictSet )
    {
        #ifdef VS_DEBUG_METHODS_X
        cout << __func__ << "2" << endl;
        #endif
        if( _conditionVectorToSimplify.size() > 1 )
        {
            set<const Condition*> redundantConditionSet = set<const Condition*>();
            unsigned posA = 0;
            unsigned posB = 0;
            /*
             * Check all condition combinations.
             */
            while( posA < _conditionVectorToSimplify.size() )
            {
                posB = posA + 1;
                while( posB < _conditionVectorToSimplify.size() )
                {
                    const Condition* condA = _conditionVectorToSimplify[posA];
                    const Condition* condB = _conditionVectorToSimplify[posB];
                    signed strongProp = smtrat::Constraint::compare( condA->pConstraint(), condB->pConstraint() );
                    /*
                     * If the two conditions have the same solution space.
                     */
                    if( strongProp == 2 )
                    {
                        /*
                         * Choose original conditions.
                         */
                        if( !condA->originalConditions().empty() &&!condB->originalConditions().empty() )
                        {
                            /*
                             * If we have to choose which original conditions to take,
                             * choose those, which have been created earlier.
                             */
                            if( condB->valuation() < condA->valuation() )
                            {
                                *condA->pOriginalConditions() = ConditionSet( condB->originalConditions() );
                                condA->rValuation()          = condB->valuation();
                            }
                        }
                        else
                        {
                            condA->pOriginalConditions()->insert( condB->originalConditions().begin(), condB->originalConditions().end() );
                        }

                        redundantConditionSet.insert( condB );

                    }
                    /*
                     * If cond1's solution space is a subset of the solution space of cond2.
                     */
                    else if( strongProp == 1 )
                    {
                        redundantConditionSet.insert( condB );
                    }
                    /*
                     * If it is easy to give a condition whose solution space is the intersection of
                     * the solution spaces of cond1 and cond2.
                     */
                    else if( strongProp == -3 )
                    {
                        if( (condA->constraint().relation() == smtrat::CR_GEQ && condB->constraint().relation() == smtrat::CR_GEQ)
                                || (condA->constraint().relation() == smtrat::CR_GEQ && condB->constraint().relation() == smtrat::CR_LEQ)
                                || (condA->constraint().relation() == smtrat::CR_LEQ && condB->constraint().relation() == smtrat::CR_GEQ)
                                || (condA->constraint().relation() == smtrat::CR_LEQ && condB->constraint().relation() == smtrat::CR_LEQ) )
                        {
                            const Condition* cond = new Condition( smtrat::Formula::newConstraint( condB->constraint().lhs(), smtrat::CR_EQ, condB->constraint().variables() ), condB->flag(), condB->originalConditions(),  condB->valuation(), true );
                            cond->pOriginalConditions()->insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                            redundantConditionSet.insert( condA );
                            redundantConditionSet.insert( condB );
                            _conditionVectorToSimplify.push_back( cond );
                            if( cond->constraint().isConsistent() == 0 )
                            {
                                ConditionSet condSet = ConditionSet();
                                condSet.insert( condA );
                                condSet.insert( condB );
                                _conflictSet.insert( condSet );
                            }
                        }
                        else if( (condA->constraint().relation() == smtrat::CR_NEQ && condB->constraint().relation() == smtrat::CR_GEQ) )
                        {
                            const Condition* cond = new Condition( smtrat::Formula::newConstraint( condB->constraint().lhs(), smtrat::CR_GREATER, condB->constraint().variables() ), condB->flag(), condB->originalConditions(),  condB->valuation(), true );
                            cond->pOriginalConditions()->insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                            redundantConditionSet.insert( condA );
                            redundantConditionSet.insert( condB );
                            _conditionVectorToSimplify.push_back( cond );
                            if( cond->constraint().isConsistent() == 0 )
                            {
                                ConditionSet condSet = ConditionSet();
                                condSet.insert( condA );
                                condSet.insert( condB );
                                _conflictSet.insert( condSet );
                            }
                        }
                        else if( (condA->constraint().relation() == smtrat::CR_GEQ && condB->constraint().relation() == smtrat::CR_NEQ) )
                        {
                            const Condition* cond = new Condition( smtrat::Formula::newConstraint( condA->constraint().lhs(), smtrat::CR_GREATER, condA->constraint().variables() ), condA->flag(), condA->originalConditions(),  condA->valuation(), true );
                            cond->pOriginalConditions()->insert( condB->originalConditions().begin(), condB->originalConditions().end() );
                            redundantConditionSet.insert( condA );
                            redundantConditionSet.insert( condB );
                            _conditionVectorToSimplify.push_back( cond );
                            if( cond->constraint().isConsistent() == 0 )
                            {
                                ConditionSet condSet = ConditionSet();
                                condSet.insert( condA );
                                condSet.insert( condB );
                                _conflictSet.insert( condSet );
                            }
                        }
                        else if( (condA->constraint().relation() == smtrat::CR_NEQ && condB->constraint().relation() == smtrat::CR_LEQ) )
                        {
                            const Condition* cond = new Condition( smtrat::Formula::newConstraint( condB->constraint().lhs(), smtrat::CR_LESS, condB->constraint().variables() ), condB->flag(), condB->originalConditions(),  condB->valuation(), true );
                            cond->pOriginalConditions()->insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                            redundantConditionSet.insert( condA );
                            redundantConditionSet.insert( condB );
                            _conditionVectorToSimplify.push_back( cond );
                            if( cond->constraint().isConsistent() == 0 )
                            {
                                ConditionSet condSet = ConditionSet();
                                condSet.insert( condA );
                                condSet.insert( condB );
                                _conflictSet.insert( condSet );
                            }
                        }
                        else if( (condA->constraint().relation() == smtrat::CR_LEQ && condB->constraint().relation() == smtrat::CR_NEQ) )
                        {
                            const Condition* cond = new Condition( smtrat::Formula::newConstraint( condA->constraint().lhs(), smtrat::CR_LESS, condA->constraint().variables() ), condA->flag(), condA->originalConditions(),  condA->valuation(), true );
                            cond->pOriginalConditions()->insert( condB->originalConditions().begin(), condB->originalConditions().end() );
                            redundantConditionSet.insert( condA );
                            redundantConditionSet.insert( condB );
                            _conditionVectorToSimplify.push_back( cond );
                            if( cond->constraint().isConsistent() == 0 )
                            {
                                ConditionSet condSet = ConditionSet();
                                condSet.insert( condA );
                                condSet.insert( condB );
                                _conflictSet.insert( condSet );
                            }
                        }
                        else
                        {
                            assert( false );
                        }
                    }
                    /*
                     * If cond1's solution space is a superset of the solution space of cond2.
                     */
                    else if( strongProp == -1 )
                    {
                        redundantConditionSet.insert( condA );
                    }
                    /*
                     * If it is easy to decide that cond1 and cond2 are conflicting.
                     */
                    else if( strongProp == -2 || strongProp == -4 )
                    {
                        ConditionSet condSet = ConditionSet();
                        condSet.insert( condA );
                        condSet.insert( condB );

                        _conflictSet.insert( condSet );
                    }
                    ++posB;
                }
                ++posA;
            }

            /*
             * Delete the conflicting conditions from redundant conditions.
             */
            ConditionSetSet::iterator condSet = _conflictSet.begin();
            while( condSet != _conflictSet.end() )
            {
                ConditionSet::iterator cond = condSet->begin();
                while( cond != condSet->end() )
                {
                    redundantConditionSet.erase( *cond++ );
                }
                ++condSet;
            }

            /*
             * Delete the redundant conditions of the vector of conditions to simplify.
             */
            ConditionVector::iterator cond = _conditionVectorToSimplify.begin();
            while( cond != _conditionVectorToSimplify.end() )
            {
                if( redundantConditionSet.find( *cond ) != redundantConditionSet.end() )
                {
                    cond = _conditionVectorToSimplify.erase( cond );
                }
                else
                {
                    ++cond;
                }
            }
            for( set<const Condition*>::iterator redundantCond = redundantConditionSet.begin(); redundantCond != redundantConditionSet.end();
                    ++redundantCond )
            {
                _redundantConditions.push_back( *redundantCond );
            }
        }
        #ifdef VS_DEBUG_METHODS_X
        cout << "end " << __func__ << "2" << endl;
        #endif
        return _conflictSet.empty();
    }

    /**
     * Sets the index of this state.
     *
     * @param _index The string to which the index should be set.
     */
    void State::setIndex( const string& _index )
    {
        if( _index.compare( "0" ) == 0 || _index.compare( "" ) == 0 )
        {
            *mpIndex = _index;
        }
        else
        {
            *mpIndex = _index;

            for( ConditionVector::iterator cond = rConditions().begin(); cond != conditions().end(); ++cond )
            {
                /*
                 * Does the condition contain the variable we can generate
                 * test candidates for.
                 */
                if( (**cond).constraint().variables().find( index() ) == (**cond).constraint().variables().end() )
                {
                    (**cond).rFlag() = true;
                }
                else
                {
                    #ifdef SMTRAT_VS_VARIABLEBOUNDS_B
                    (**cond).rFlag() = hasNoRootsInVariableBounds( *cond );
                    #else
                    (**cond).rFlag() = false;
                    #endif
                    
                }
            }
        }
    }

    /**
     * Sets the ID of the state.
     *
     * @param _id   The new value for the ID of this state.
     *
     * @return  true    ,if the ID to set is smaller the maximal possible id.
     *          false   ,else.
     */
    bool State::setID( const unsigned _id )
    {
        if( _id < MAX_ID )
        {
            mID = _id;
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * Adds a conflict set to the map of substitutions to conflict sets.
     *
     * @param _substitution The corresponding substitution generated the conflict.
     *                      (NULL in the case a detected conflict without substitution)
     * @param _condSetSet   The conflicts to add.
     */
    void State::addConflictSet( const Substitution* const _substitution, ConditionSetSet& _condSetSet )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif
        ConflictSets::iterator iter = mpConflictSets->find( _substitution );
        if( iter != mpConflictSets->end() )
        {
            iter->second.insert( _condSetSet );
        }
        else
        {
            ConditionSetSetSet condSetSetSet = ConditionSetSetSet();
            condSetSetSet.insert( _condSetSet );
            mpConflictSets->insert( pair<const Substitution* const , ConditionSetSetSet>( _substitution, condSetSetSet ) );
        }
        if( _substitution == NULL )
        {
            rInconsistent() = true;
        }
    }

    /**
     * Adds all conflicts to all sets of the conflict set of the given substitution.
     *
     * @param _substitution The corresponding substitution generated the conflict.
     *                      (NULL in the case a detected conflict without substitution)
     * @param _condSetSet   The conflicts to add.
     */
    void State::addConflicts( const Substitution* const _substitution, ConditionSetSet& _condSetSet )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif
        ConflictSets::iterator iter = mpConflictSets->find( _substitution );
        if( iter != mpConflictSets->end() )
        {
            ConditionSetSetSet newCondSetSetSet = ConditionSetSetSet();
            for( ConditionSetSetSet::iterator condSetSet = iter->second.begin(); condSetSet != iter->second.end(); ++condSetSet )
            {
                ConditionSetSet newCondSetSet = ConditionSetSet();
                newCondSetSet.insert( condSetSet->begin(), condSetSet->end() );
                newCondSetSet.insert( _condSetSet.begin(), _condSetSet.end() );
                newCondSetSetSet.insert( newCondSetSet );
            }
            iter->second = newCondSetSetSet;
        }
        else
        {
            ConditionSetSetSet condSetSetSet = ConditionSetSetSet();
            condSetSetSet.insert( _condSetSet );
            mpConflictSets->insert( pair<const Substitution* const , ConditionSetSetSet>( _substitution, condSetSetSet ) );
        }
    }

    void State::resetConflictSets()
    {
        if( !mpConflictSets->empty() )
        {

            auto conflictSet = mpConflictSets->begin();
            if( conflictSet->first == NULL )
            {
                ++conflictSet;
            }
            mpConflictSets->erase( conflictSet, mpConflictSets->end() );
        }
    }

    /**
     * Updates the original conditions of substitutions having the same test candidate as the
     * given.
     *
     * @param   _substitution   The substitution containing the test candidate to check for.
     *
     * @return  true,   If the test candidate of the given substitution was already generated;
     *          false,  otherwise.
     */
    bool State::updateOCondsOfSubstitutions( const Substitution& _substitution )
    {
        for( StateVector::iterator child = rChildren().begin(); child != children().end(); ++child )
        {
            // TODO: If there is a child with a test candidate whose side conditions are a superset of the side conditions of the
            // given substitution, remove the child and add the test candidates original conditions to the original conditions of
            // the given substitution. However, when deleting later the original condition of the given substitution, the its
            // getting nasty.
            if( (**child).substitution() == _substitution )
            {
                (**child).rSubstitution().rOriginalConditions().insert( _substitution.originalConditions().begin(),
                                                                        _substitution.originalConditions().end() );
                return true;
            }
        }
        return false;
    }

    /**
     * Adds the given substitution results to this state.
     *
     * @param   _disjunctionsOfCondConj     The substitution results given by a vector
     *                                  of disjunctions of conjunctions of conditions.
     */
    void State::addSubstitutionResults( vector<DisjunctionOfConditionConjunctions>& _disjunctionsOfCondConj )
    {
        #ifdef VS_DEBUG_METHODS_X
        cout << __func__ << endl;
        #endif
        /*
         * For each disjunction add a substitution result to the substitution results of this state.
         */
        if( mpSubstitutionResults == NULL )
        {
            mpSubstitutionResults = new SubstitutionResults();
        }
        for( vector<DisjunctionOfConditionConjunctions>::iterator disjunction = _disjunctionsOfCondConj.begin();
                disjunction != _disjunctionsOfCondConj.end(); ++disjunction )
        {
            mpSubstitutionResults->push_back( SubstitutionResult() );
            for( DisjunctionOfConditionConjunctions::iterator conjunction = disjunction->begin(); conjunction != disjunction->end(); ++conjunction )
            {
                mpSubstitutionResults->back().push_back( pair<ConditionVector, bool>( *conjunction, false ) );
            }
        }
        /*
         * Mark this state as not yet simplified.
         */
        mSubResultsSimplified = false;
        mToHighDegree         = false;
        mMarkedAsDeleted      = false;
        mStateType            = COMBINE_SUBRESULTS;
    }

    /**
     * Extend the currently considered combination of conjunctions in the substitution results.
     */
    bool State::extendSubResultCombination()
    {
        #ifdef VS_DEBUG_METHODS_X
        cout << __func__ << endl;
        #endif
        assert( subResultsSimplified() );

        if( mpSubResultCombination == NULL )
        {
            mpSubResultCombination = new SubResultCombination();
        }

        if( mpSubResultCombination->size() < mpSubstitutionResults->size() )
        {
            unsigned bestSubResultIndex          = 0;
            bool     notConsideredSubResultFound = false;
            unsigned subResultIndex              = 0;
            while( subResultIndex < mpSubstitutionResults->size() )
            {
                /*
                 * Set all flags of conjunctions of conditions in the substitution result to false.
                 */
                SubstitutionResult::iterator condConj = mpSubstitutionResults->at( subResultIndex ).begin();
                while( condConj != mpSubstitutionResults->at( subResultIndex ).end() )
                {
                    condConj->second = false;
                    ++condConj;
                }

                /*
                 * Check whether the sub result has not yet been considered.
                 */
                bool                                 subResultAlreadyConsidered = false;
                SubResultCombination::const_iterator subResComb                 = mpSubResultCombination->begin();
                while( subResComb != mpSubResultCombination->end() )
                {
                    if( subResComb->first == subResultIndex )
                    {
                        subResultAlreadyConsidered = true;
                        break;
                    }
                    ++subResComb;
                }

                if( !subResultAlreadyConsidered )
                {
                    if( notConsideredSubResultFound )
                    {
                        /*
                         * We have already a currently best substitution result and check if
                         * it is better than the substitution result we consider now.
                         */
                        unsigned subResultSize = mpSubstitutionResults->at( subResultIndex ).size();

                        assert( subResultSize > 0 );

                        if( subResultSize < mpSubstitutionResults->at( bestSubResultIndex ).size() )
                        {
                            bestSubResultIndex = subResultIndex;
                        }
                    }
                    else
                    {
                        /*
                         * This is the first not yet considered substitution result, so
                         * add take it as the currently best one.
                         */
                        assert( mpSubstitutionResults->at( subResultIndex ).size() > 0 );
                        bestSubResultIndex          = subResultIndex;
                        notConsideredSubResultFound = true;
                    }
                }
                ++subResultIndex;
            }

            /*
             * Add the found substitution result to the substitution result combinations.
             */
            mpSubResultCombination->push_back( pair<unsigned, unsigned>( bestSubResultIndex, 0 ) );
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * If the state contains a substitution result, which is a conjunction of disjunctions of
     * conjunctions of conditions, this method sets the current combination to the disjunctions
     * to the next combination.
     *
     * @return  true,   if there is a next combination;
     *          false,  otherwise.
     */
    bool State::nextSubResultCombination()
    {
        #ifdef VS_DEBUG_METHODS_X
        cout << __func__ << endl;
        #endif
        assert( stateType() == COMBINE_SUBRESULTS );

        if( !hasSubResultsCombination() )
        {
            extendSubResultCombination();
            return true;
        }
        else
        {
            assert( mpSubResultCombination->size() <= mpSubstitutionResults->size() );

            if( takeSubResultCombAgain() )
            {
                mTakeSubResultCombAgain = false;
            }
            else
            {
                SubResultCombination::reverse_iterator rIter = mpSubResultCombination->rbegin();
                while( rIter != mpSubResultCombination->rend() )
                {
                    /*
                     * Take the next conjunction of conditions of the considered substitution result, which
                     * has the flag false.
                     */
                    mpSubstitutionResults->at( rIter->first ).at( rIter->second ).second = true;
                    while( rIter->second < mpSubstitutionResults->at( rIter->first ).size() - 1
                            && mpSubstitutionResults->at( rIter->first ).at( rIter->second ).second )
                    {
                        ++(rIter->second);
                    }

                    /*
                     * If it has already been the last conjunction of conditions of the considered substitution result.
                     */
                    if( rIter->second == mpSubstitutionResults->at( rIter->first ).size() - 1
                            && mpSubstitutionResults->at( rIter->first ).at( rIter->second ).second )
                    {
                        /*
                         * Check if we already have reached the first substitution result.
                         */
                        SubResultCombination::const_reverse_iterator rIterTemp = rIter;
                        ++rIterTemp;

                        /*
                         * If we currently consider the first substution result, return false,
                         * which means, that there is no other combination to consider.
                         */
                        if( rIterTemp == mpSubResultCombination->rend() )
                        {
                            return false;
                        }

                        /*
                         * Otherwise, go back the first conjunction of conditions of the currently
                         * considered substitution result and try to go to the next conjunction of
                         * conditions in the next substitution result.
                         */
                        else
                        {
                            for( SubstitutionResult::iterator condConj = mpSubstitutionResults->at( rIter->first ).begin();
                                    condConj != mpSubstitutionResults->at( rIter->first ).end(); ++condConj )
                            {
                                condConj->second = false;
                            }
                            rIter->second = 0;
                        }
                    }

                    /*
                     * Otherwise we found a valid new combination of conjunction of conditions.
                     */
                    else
                    {
                        return true;
                    }
                    ++rIter;
                }
            }

            /*
             * A valid new combination of substitution results is established.
             */
            return true;
        }
    }

    /**
     *
     */
    const ConditionVector State::getCurrentSubresultCombination() const
    {
        ConditionVector currentSubresultCombination = ConditionVector();
        SubResultCombination::const_iterator iter = mpSubResultCombination->begin();
        while( iter != mpSubResultCombination->end() )
        {
            for( ConditionVector::const_iterator cond = mpSubstitutionResults->at( iter->first ).at( iter->second ).first.begin();
                    cond != mpSubstitutionResults->at( iter->first ).at( iter->second ).first.end(); ++cond )
            {
                currentSubresultCombination.push_back( new Condition( **cond ) );
            }
            ++iter;
        }
        return currentSubresultCombination;
    }

    /**
     * Determines the condition vector corresponding to the current combination of the
     * conjunctions of conditions.
     */
    bool State::refreshConditions()
    {
        #ifdef VS_DEBUG_METHODS_X
        cout << __func__ << endl;
        #endif
        assert( stateType() == COMBINE_SUBRESULTS );

        bool conditionsChanged = false;
        if( !mpSubstitutionResults->empty() )
        {
            /*
             * Get the conditions of the currently considered combination of substitution results.
             */
            ConditionVector newCombination = getCurrentSubresultCombination();

            /*
             * Simplify the conditions already here, to avoid unnecessarily adding and deleting conditions.
             */
            ConditionVector redundantConditions       = ConditionVector();
            ConditionSetSet conflictingConditionPairs = ConditionSetSet();
            if( !simplify( newCombination, redundantConditions, conflictingConditionPairs ) )
            {
                rInconsistent() = true;
            }
            while( !redundantConditions.empty() )
            {
                const Condition* toDelete = redundantConditions.back();
                redundantConditions.pop_back();
                delete toDelete;
            }

            /*
             * Delete the conditions of this combination, which do already occur in the considered conditions
             * of this state.
             */
            ConditionVector condsToDelete = ConditionVector();
            ConditionVector::iterator cond = rConditions().begin();
            while( cond != conditions().end() )
            {
                /*
                 * Check if the condition occurs in the new combination. If so, delete
                 * the corresponding condition in the new combination.
                 */
                bool                      condOccursInNewConds = false;
                ConditionVector::iterator newCond              = newCombination.begin();
                while( newCond != newCombination.end() )
                {
                    if( (**cond).constraint() == (**newCond).constraint() )
                    {
                        /*
                         * Choose original conditions.
                         */
                        if( !(**cond).originalConditions().empty() &&!(**newCond).originalConditions().empty() )
                        {
                            /*
                             * If we have to choose which original conditions to take,
                             * choose those, which have been created earlier.
                             */
                            if( (**newCond).valuation() < (**cond).valuation() )
                            {
                                *(**cond).pOriginalConditions() = ConditionSet( (**newCond).originalConditions() );
                                (**cond).rValuation()          = (**newCond).valuation();
                            }
                        }
                        else
                        {
                            (**cond).pOriginalConditions()->insert( (**newCond).originalConditions().begin(), (**newCond).originalConditions().end() );
                        }
                        const Condition* pCond = *newCond;
                        newCombination.erase( newCond );
                        delete pCond;
                        condOccursInNewConds = true;
                        break;
                    }
                    else
                    {
                        ++newCond;
                    }
                }

                /*
                 * Remember the condition not occuring in the current combination.
                 */
                if( !condOccursInNewConds )
                {
                    condsToDelete.push_back( *cond );
                    conditionsChanged = true;
                }
                ++cond;
            }
            if( !newCombination.empty() )
            {
                conditionsChanged = true;
            }

            /*
             * Delete the conditions, which do not occur in the current combination.
             */
            if( !condsToDelete.empty() )
            {
                deleteConditions( condsToDelete );
                while( !condsToDelete.empty() )
                {
                    const vs::Condition* toDelete = condsToDelete.back();
                    condsToDelete.pop_back();
                    delete toDelete;
                }
            }

            /*
             * Add the remaining conditions of the current combination to the conditions
             * this state considers.
             */
            for( ConditionVector::const_iterator newCond = newCombination.begin(); newCond != newCombination.end(); ++newCond )
            {
                addCondition( (**newCond).pConstraint(), (**newCond).originalConditions(), (**newCond).valuation(), true );
            }
            while( !newCombination.empty() )
            {
                const Condition*& rpCond = newCombination.back();
                newCombination.pop_back();
                delete rpCond;
            }
        }
        mStateType = TEST_CANDIDATE_TO_GENERATE;
        if( conditionsChanged )
        {
            mConditionsSimplified = false;
            mTryToRefreshIndex    = true;
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * Sets all flags of the conditions to true, if it contains the variable given by the states index.
     */
    void State::initConditionFlags()
    {
        for( ConditionVector::iterator cond = rConditions().begin(); cond != conditions().end(); ++cond )
        {
            if( (**cond).constraint().hasVariable( index() ) )
            {
                (**cond).rFlag() = false;
            }
        }
    }

    /**
     * Sets, if it has not already happened, the index of the state to the name of the
     * most adequate variable. Which variable is taken depends on heuristics.
     *
     * @param   _allVariables   All globally known variables.
     */
    bool State::initIndex( const symtab& _allVariables )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif

        mTryToRefreshIndex = false;

        if( conditions().empty() )
        {
            return false;
        }

        map<string, multiset<double> > varVals = map<string, multiset<double> >();
        for( symtab::const_iterator var = _allVariables.begin(); var != _allVariables.end(); ++var )
        {
            varVals.insert( pair<string, multiset<double> >( var->first, multiset<double>() ) );
        }

        /*
         * Find for each variable the highest valuation of all conditions' constraints.
         */
        for( ConditionVector::const_iterator cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            /*
             * Check for all variables their valuation for the given constraint.
             */
            for( map<string, multiset<double> >::iterator var = varVals.begin(); var != varVals.end(); ++var )
            {
                double varInConsVal = (**cond).valuate( var->first, _allVariables.size(), true );
                if( varInConsVal != 0 )
                {
                    varVals.at( var->first ).insert( varInConsVal );
                }
            }
        }

        #ifdef VS_DEBUG_METHODS_X
        for( map<string, multiset<double> >::const_iterator var = varVals.begin(); var != varVals.end(); ++var )
        {
            cout << var->first << ":  ";
            for( multiset<double>::const_iterator varVal = var->second.begin(); varVal != var->second.end(); ++varVal )
            {
                cout <<  setprecision(10) << *varVal << " | ";
            }
            cout << endl;
        }
        #endif

        /*
         * Find the variable which has in a constraint the best valuation. If more than one
         * have the highest valuation, then choose the one having the higher valuation
         * according to the method argument "_allVariables".
         */
        map<string, multiset<double> >::const_iterator bestVar = varVals.begin();
        map<string, multiset<double> >::const_iterator var     = varVals.begin();
        ++var;
        while( var != varVals.end() )
        {
            if( !var->second.empty() &&!bestVar->second.empty() )
            {
                if( var->second.size() == 1 && bestVar->second.size() == 1 )
                {
                    if( *var->second.begin() < *bestVar->second.begin() )
                    {
                        bestVar = var;
                    }
                }
                else if( var->second.size() == 1 )
                {
                    bestVar = var;
                }
                else
                {
                    multiset<double>::const_iterator varInConsVal     = var->second.begin();
                    multiset<double>::const_iterator bestVarInConsVal = bestVar->second.begin();
                    while( varInConsVal != var->second.end() && bestVarInConsVal != bestVar->second.end() )
                    {
                        if( *varInConsVal < *bestVarInConsVal )
                        {
                            bestVar = var;
                            break;
                        }
                        else if( *varInConsVal > *bestVarInConsVal )
                        {
                            break;
                        }
                        ++varInConsVal;
                        ++bestVarInConsVal;
                    }

                    if( varInConsVal == var->second.end() && bestVarInConsVal != bestVar->second.end() )
                    {
                        bestVar = var;
                    }
                }
            }
            else if( !var->second.empty() && bestVar->second.empty() )
            {
                bestVar = var;
            }
            ++var;
        }

        if( index() == "0" || (isRoot() && index() == "") )
        {
            setIndex( (*bestVar).first );
//            cout << __func__ << "  ->  " << (*bestVar).first << endl;
            return true;
        }
        else
        {
            if( index().compare( (*bestVar).first ) != 0 )
            {
                setIndex( (*bestVar).first );
//                cout << __func__ << "  ->  " << (*bestVar).first << endl;
                return true;
            }
            return false;
        }
    }

    /**
     * Adds a constraint to the conditions of this state.
     *
     * @param _constraint           The constraint of the condition to add.
     * @param _originalConditions   The original conditions of the condition to add.
     * @param _valutation           The valuation of the condition to add.
     * @param _recentlyAdded        Is the condition a recently added one.
     *
     * @sideeffect  The state can obtain a new condition.
     */
    void State::addCondition( const smtrat::Constraint* _constraint,
                              const ConditionSet& _originalConditions,
                              const unsigned _valutation,
                              const bool _recentlyAdded )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif

        /*
         * Check if the constraint is variable-free and consistent.
         * If so, discard it.
         */
        unsigned constraintConsistency = _constraint->isConsistent();

        assert( constraintConsistency != 0 );

        if( constraintConsistency != 1 )
        {
            /*
             * Check if the condition already exists.
             */
            mConditionsSimplified = false;
            mToHighDegree         = false;
            mMarkedAsDeleted      = false;

            /*
             * The state is not a leaf.
             */
            if( index() != "" && index() != "0" )
            {
                if( _recentlyAdded )
                {
                    mHasRecentlyAddedConditions = true;
                }
                bool constraintWithFinitlyManySolutionCandidatesInIndexExists = false;
                for( StateVector::const_iterator child = children().begin(); child != children().end(); ++child )
                {
                    if( (**child).pOriginalCondition() != NULL )
                    {
                        constraintWithFinitlyManySolutionCandidatesInIndexExists = true;
                    }
                    break;
                }

                /*
                 * Does the constraint contain the variable to eliminate.
                 */
                if( _constraint->variables().find( index() ) == _constraint->variables().end()
                        || constraintWithFinitlyManySolutionCandidatesInIndexExists )
                {
                    rConditions().push_back( new Condition( _constraint, true, _originalConditions, _valutation, _recentlyAdded ) );
                    #ifdef SMTRAT_VS_VARIABLEBOUNDS
                    mpVariableBounds->addBound( _constraint, rConditions().back() );
                    #endif
                }
                else
                {
                    rConditions().push_back( new Condition( _constraint, false, _originalConditions, _valutation, _recentlyAdded ) );
                    #ifdef SMTRAT_VS_VARIABLEBOUNDS
                    mpVariableBounds->addBound( _constraint, rConditions().back() );
                    #endif
                }
            }

            /*
             * The state is a leaf.
             */
            else
            {
                rConditions().push_back( new Condition( _constraint, false, _originalConditions, _valutation, false ) );
                #ifdef SMTRAT_VS_VARIABLEBOUNDS
                mpVariableBounds->addBound( _constraint, rConditions().back() );
                #endif
            }
        }
    }
    
    /**
     * Removes everything in this state originated by the given vector of conditions.
     * 
     * @param _originsToDelete The conditions for which everything in this state which
     *                          has been originated by them must be removed.
     * 
     * @return 0,  if this state got invalid and must be deleted afterwards;
     *          -1, if this state got invalid and must be deleted afterwards
     *              and made other states unnecessary to consider;
     *          1,  otherwise.
     */
    int State::deleteOrigins( ConditionVector& _originsToDelete )
    {
        if( _originsToDelete.empty() ) return 1;
        if( !isRoot() )
        {
            // Check if the substitution has a condition to delete as original condition.
            for( auto condToDel = _originsToDelete.begin(); condToDel != _originsToDelete.end(); ++condToDel )
            {
                ConditionSet::iterator oCondInSub = rSubstitution().rOriginalConditions().begin();
                while( oCondInSub != substitution().originalConditions().end() )
                {
                    if( *oCondInSub == *condToDel )
                    {
                        rSubstitution().rOriginalConditions().erase( oCondInSub++ );
                    }
                    else
                    {
                        ++oCondInSub;
                    }
                }
                if( substitution().originalConditions().empty() )
                {
                    // If the substitutions original conditions are all deleted, then delete the corresponding child.
                    // TODO: Maybe it is better to keep these children/test candidates.
                    int result = 0;
                    if( pOriginalCondition() != NULL )
                    {
                        result = -1;
                    }
                    return result;
                }
            }
        }

        // Remove conditions from the currently considered condition vector, which are originated by any of the given origins.
        bool conditionDeleted = false;
        bool recentlyAddedConditionLeft = false;
        ConditionVector deletedConditions = ConditionVector();
        for( auto originToDelete = _originsToDelete.begin(); originToDelete != _originsToDelete.end(); ++originToDelete )
        {
            auto condition = rConditions().begin();
            while( condition != conditions().end() )
            {
                if( (*condition)->originalConditions().find( *originToDelete ) != (*condition)->originalConditions().end() )
                {
                    #ifdef SMTRAT_VS_VARIABLEBOUNDS
                    mpVariableBounds->removeBound( (*condition)->pConstraint(), *condition );
                    #endif
                    deletedConditions.push_back( *condition );
                    condition = rConditions().erase( condition );
                    conditionDeleted = true;
                }
                else
                {
                    if( (*condition)->recentlyAdded() ) recentlyAddedConditionLeft = true;
                    ++condition;
                }
            }
        }
        if( conditionDeleted )
        {
            if( !isRoot() )
            {
                mTakeSubResultCombAgain = true;
                mStateType              = COMBINE_SUBRESULTS;
            }
            mInconsistent = false;
            mHasRecentlyAddedConditions = recentlyAddedConditionLeft;
        }
        mToHighDegree      = false;
        mMarkedAsDeleted   = false;
        mTryToRefreshIndex = true;

        // Delete everything originated by it in all children of this state.
        deleteOriginsFromChildren( deletedConditions );

        // Delete the conditions in the conflict sets which are originated by any of the given origins.
        deleteOriginsFromConflictSets( _originsToDelete, false );
        
        // Delete the conditions.
        while( !deletedConditions.empty() )
        {
            const Condition* pCond = deletedConditions.back();
            deletedConditions.pop_back();
            delete pCond;
        }

        // Delete all conditions in the substitution result which are originated by any of the 
        // given origins and adapt the currently considered substitution result combination.
        deleteOriginsFromSubstitutionResults( _originsToDelete );
        return 1;
    }

    /**
     * Delete everything originated by the given conditions from the entire subtree with
     * this state as root.
     *
     * @param _conditionsToDelete The conditions to delete.
     */
    void State::deleteConditions( ConditionVector& _conditionsToDelete )
    {
        if( _conditionsToDelete.empty() ) return;
        
        // Delete everything originated by the given conditions in all children of this state.
        deleteOriginsFromChildren( _conditionsToDelete );

        // Delete the conditions from the conflict sets.
        deleteOriginsFromConflictSets( _conditionsToDelete, true );

        // Delete everything originated by the conditions to delete in the state's children.
        deleteOriginsFromChildren( _conditionsToDelete );

        bool conditionDeleted = false;
        bool recentlyAddedConditionLeft = false;
        for( auto cond = rConditions().begin(); cond != conditions().end(); )
        {
            // Delete the condition from the vector this state considers.
            ConditionVector::iterator condToDel = _conditionsToDelete.begin();
            while( condToDel != _conditionsToDelete.end() )
            {
                if( *cond == *condToDel ) break;
                ++condToDel;
            }
            if( condToDel != _conditionsToDelete.end() )
            {
                #ifdef SMTRAT_VS_VARIABLEBOUNDS
                mpVariableBounds->removeBound( (*cond)->pConstraint(), *cond );
                #endif
                conditionDeleted = true;
                cond = rConditions().erase( cond );
            }
            else
            {
                if( (*cond)->recentlyAdded() ) recentlyAddedConditionLeft = true;
                ++cond;
            }
        }
        if( conditionDeleted )
        {
            if( !isRoot() )
            {
                mTakeSubResultCombAgain = true;
                mStateType              = COMBINE_SUBRESULTS;
            }
            mInconsistent = false;
            mHasRecentlyAddedConditions = recentlyAddedConditionLeft;
        }

        mToHighDegree      = false;
        mMarkedAsDeleted   = false;
        mTryToRefreshIndex = true;
    }
    
    /**
     * 
     * @param _originsToDelete
     */
    void State::deleteOriginsFromChildren( ConditionVector& _originsToDelete )
    {
        auto child = rChildren().begin();
        while( child != children().end() )
        {
            int result = (*child)->deleteOrigins( _originsToDelete );
            if( result < 0 )
            {
                initConditionFlags();
            }
            if( result < 1 )
            {
                ConflictSets::iterator conflictSet = rConflictSets().find( (*child)->pSubstitution() );
                if( conflictSet != conflictSets().end() )
                {
                    rConflictSets().erase( conflictSet );
                }
                State* toDelete = *child;
                child = rChildren().erase( child );
                delete toDelete;
            }
            else
            {
                ++child;
            }
        }
    }
    
    /**
     * 
     * @param _originsToDelete
     */
    void State::deleteOriginsFromConflictSets( ConditionVector& _originsToDelete, bool _originsAreCurrentConditions )
    {
        ConflictSets::iterator conflictSet = mpConflictSets->begin();
        while( conflictSet != mpConflictSets->end() )
        {
            ConditionSetSetSet updatedCondSetSetSet = ConditionSetSetSet();
            ConditionSetSetSet::iterator condSetSet         = conflictSet->second.begin();
            bool                         emptyReasonOccured = false;
            while( condSetSet != conflictSet->second.end() )
            {
                ConditionSetSet updatedCondSetSet = ConditionSetSet();
                ConditionSetSet::iterator condSet = condSetSet->begin();
                while( condSet != condSetSet->end() )
                {
                    ConditionSet updatedCondSet = ConditionSet();
                    ConditionSet::iterator cond             = condSet->begin();
                    bool                   condToDelOccured = false;
                    while( cond != condSet->end() )
                    {
                        ConditionVector::const_iterator condToDel = _originsToDelete.begin();
                        while( condToDel != _originsToDelete.end() )
                        {
                            if( _originsAreCurrentConditions )
                            {
                                if( *cond == *condToDel )
                                {
                                    break;
                                }
                            }
                            else
                            {
                                if( (*cond)->originalConditions().find( *condToDel ) != (*cond)->originalConditions().end() )
                                {
                                    break;
                                }
                            }
                            ++condToDel;
                        }
                        if( condToDel == _originsToDelete.end() )
                        {
                            updatedCondSet.insert( *cond );
                        }
                        else
                        {
                            condToDelOccured = true;
                            break;
                        }
                        ++cond;
                    }
                    if( !condToDelOccured )
                    {
                        updatedCondSetSet.insert( updatedCondSet );
                    }
                    ++condSet;
                }
                if( !updatedCondSetSet.empty() )
                {
                    updatedCondSetSetSet.insert( updatedCondSetSet );
                }
                else
                {
                    emptyReasonOccured = true;
                    break;
                }
                ++condSetSet;
            }
            if( !emptyReasonOccured )
            {
                conflictSet->second = updatedCondSetSetSet;
                ++conflictSet;
            }
            else
            {
                if( conflictSet->first == NULL )
                {
                    rInconsistent() = false;
                }
                #ifdef SMTRAT_VS_VARIABLEBOUNDS_B
                if( conflictSet->first != NULL && conflictSet->first->type() == ST_INVALID )
                {
                    const Substitution* subToDelete = conflictSet->first;
                    mpConflictSets->erase( conflictSet++ );
                    delete subToDelete;
                }
                else
                {
                #endif
                    mpConflictSets->erase( conflictSet++ );
                #ifdef SMTRAT_VS_VARIABLEBOUNDS_B
                }
                #endif
            }
        }

        auto child = rChildren().begin();
        while( child != children().end() )
        {
            if( mpConflictSets->find( (*child)->pSubstitution() ) == mpConflictSets->end() )
            {
                /*
                 * Delete the entry of the test candidate whose conflict set is empty
                 * and set "inconsistent flag" of the corresponding child to false.
                 */
                if( (*child)->hasSubstitutionResults() )
                {
                    if( (*child)->hasSubResultsCombination() )
                    {
                        SubResultCombination::iterator subResComb = (**child).rSubResultCombination().begin();
                        while( subResComb != (*child)->subResultCombination().end() )
                        {
                            subResComb->second = 0;
                            ++subResComb;
                        }
                    }
                    SubstitutionResults::iterator subResult = (*child)->rSubstitutionResults().begin();
                    while( subResult != (*child)->substitutionResults().end() )
                    {
                        SubstitutionResult::iterator condConj = subResult->begin();
                        while( condConj != subResult->end() )
                        {
                            condConj->second = false;
                            ++condConj;
                        }
                        ++subResult;
                    }
                }
                if( (*child)->stateType() != SUBSTITUTION_TO_APPLY )
                {
                    (*child)->rStateType() = COMBINE_SUBRESULTS;
                    (*child)->rTakeSubResultCombAgain() = true;
                }
                (*child)->rInconsistent() = false;
            }
            ++child;
        }
    }
    
    /**
     * 
     * @param _originsToDelete
     */
    void State::deleteOriginsFromSubstitutionResults( ConditionVector& _originsToDelete )
    {
        if( hasSubstitutionResults() )
        {
            unsigned                      subResultIndex = 0;
            SubstitutionResults::iterator subResult      = rSubstitutionResults().begin();
            while( subResult != substitutionResults().end() )
            {
                unsigned                     subResultConjunctionIndex = 0;
                SubstitutionResult::iterator condConj                  = subResult->begin();
                while( condConj != subResult->end() )
                {
                    ConditionVector conditionsToAdd = ConditionVector();
                    ConditionVector::iterator cond = condConj->first.begin();
                    while( cond != condConj->first.end() )
                    {
                        bool                   oCondsDeleted = false;
                        ConditionSet::iterator oCond         = (**cond).pOriginalConditions()->begin();
                        while( oCond != (**cond).originalConditions().end() )
                        {
                            ConditionVector::const_iterator condToDel = _originsToDelete.begin();
                            while( condToDel != _originsToDelete.end() )
                            {
                                if( *oCond == *condToDel )
                                {
                                    break;
                                }
                                ++condToDel;
                            }
                            if( condToDel != _originsToDelete.end() )
                            {
                                (**cond).pOriginalConditions()->erase( oCond++ );
                                oCondsDeleted = true;
                            }
                            else
                            {
                                ++oCond;
                            }
                        }
                        if( oCondsDeleted )
                        {
                            oCond = (**cond).pOriginalConditions()->begin();
                            while( oCond != (**cond).originalConditions().end() )
                            {
                                ConditionSet oConds = ConditionSet();
                                oConds.insert( *oCond );
                                conditionsToAdd.push_back( new Condition( (**oCond).pConstraint(), false, oConds, (**cond).valuation() ) );
                                ++oCond;
                            }
                            const Condition* rpCond = *cond;
                            cond             = condConj->first.erase( cond );
                            condConj->second = false;
                            delete rpCond;
                            rSubResultsSimplified() = false;
                        }
                        else
                        {
                            ++cond;
                        }
                    }

                    condConj->first.insert( condConj->first.end(), conditionsToAdd.begin(), conditionsToAdd.end() );

                    if( condConj->first.empty() )
                    {
                        if( hasSubResultsCombination() )
                        {
                            // If the currently considered substitution result is part of the substitution result combination of this state.
                            SubResultCombination::iterator subResComb = rSubResultCombination().begin();
                            while( subResComb != rSubResultCombination().end() && subResComb->first != subResultIndex )
                            {
                                ++subResComb;
                            }
                            if( subResComb != subResultCombination().end() )
                            {
                                /*
                                 * If the currently considered condition conjunction in the currently considered substitution result
                                 * is part of the substitution result combination of this state.
                                 */
                                if( subResComb->second == subResultConjunctionIndex )
                                {
                                    // Remove this entry of the substitution result combinations.
                                    rSubResultCombination().erase( subResComb );
                                }

                                /*
                                 * If the currently considered condition conjunction in the currently considered substitution result
                                 * is NOT part of the substitution result combination of this state, but another condition conjunction in
                                 * the currently considered substitution result with higher index, decrease this index.
                                 */
                                else if( subResComb->second > subResultConjunctionIndex )
                                {
                                    --(subResComb->second);
                                }
                            }
                            if( subResult->size() == 1 )
                            {
                                SubResultCombination::iterator subResCombB = rSubResultCombination().begin();
                                while( subResCombB != subResultCombination().end() )
                                {
                                    if( subResCombB->first > subResultIndex )
                                    {
                                        --(subResCombB->first);
                                    }
                                    ++subResCombB;
                                }
                            }
                        }
                        condConj = subResult->erase( condConj );
                    }
                    else
                    {
                        ++condConj;
                        ++subResultConjunctionIndex;
                    }
                }

                // Remove the substitution result if it is empty.
                if( subResult->empty() )
                {
                    subResult = rSubstitutionResults().erase( subResult );
                }
                else
                {
                    ++subResult;
                    ++subResultIndex;
                }
            }
        }
    }

    /**
     * Adds a state as child to this state. The substitution term is
     * either infinity or -infinity.
     *
     * @param _eliminationVar       The variable, which was eliminated and now is
     *                              element of a substitution.
     * @param _substitutionType     The type of the substitution we create.
     *
     * @return  1,  if a state was successfully added;
     *          0,  if a the state already exists;
     *         -1,  if the side conditions fail.
     */
    int State::addChild( const string& _eliminationVar, const ex& _elimVarAsEx, const Substitution_Type& _substitutionType, const ConditionSet& _oConditions )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif
        Substitution sub = Substitution( _eliminationVar, _elimVarAsEx, _substitutionType, _oConditions );
        if( !updateOCondsOfSubstitutions( sub ) )
        {
            State * dt = new State( this, sub );
            (*dt).updateValuation();
            rChildren().push_back( dt );
            return 1;
        }
        else
        {
            return 0;
        }
    }

    /**
     * Adds a state as child to this state. The conditions are formed
     * by a condition vector plus a new condition.
     *
     * @param _oldConditions        The conditions of this state, minus the one
     *                              used to eliminate the according variable.
     * @param _lhsCondition         The left hand side of the first condition.
     * @param _relationCondition    The relation symbol of the first condition.
     * @param _eliminationVar       The variable, which was eliminated and now is
     *                              element of a substitution.
     * @param _subTermNum           The numerator of the term to which the variable is mapped.
     * @param _subTermDenom         The denominator of the term to which the variable is mapped.
     * @param _substitutionType     The type of the substitution we create.
     *
     * @return  1,  if a state was successfully added;
     *          0,  if a the state already exists;
     *         -1,  if the side conditions fail.
     */
    int State::addChild( const ex& _lhsCondition,
                          const smtrat::Constraint_Relation& _relationCondition,
                          const string& _eliminationVar,
                          const ex& _elimVarAsEx,
                          const ex& _subTermConstPart,
                          const ex& _subTermFactor,
                          const ex& _subTermDenom,
                          const ex& _subTermRadicand,
                          const Substitution_Type& _substitutionType,
                          const symtab& _variables,
                          const ConditionSet& _oConditions )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif
        const smtrat::Constraint* cons = smtrat::Formula::newConstraint( _lhsCondition, _relationCondition, _variables );
        unsigned isConsConsistent = (*cons).isConsistent();
        if( isConsConsistent != 0 )
        {
            SqrtEx sqEx = SqrtEx( _subTermConstPart, _subTermFactor, _subTermDenom, _subTermRadicand, _variables );

            smtrat::ConstraintSet sideCond = smtrat::ConstraintSet();
            if( isConsConsistent != 1 ) sideCond.insert( cons );

            Substitution sub = Substitution( _eliminationVar, _elimVarAsEx, sqEx, _substitutionType, _oConditions, sideCond );
            if( !updateOCondsOfSubstitutions( sub ) )
            {
                State* state = new State( this, sub );

                if( isConsConsistent != 1 )
                {
                    std::vector<DisjunctionOfConditionConjunctions> subResults = std::vector<DisjunctionOfConditionConjunctions>();
                    subResults.push_back( DisjunctionOfConditionConjunctions() );
                    subResults.back().push_back( ConditionVector() );

                    subResults.back().back().push_back( new Condition( *sideCond.begin(), false, _oConditions, (*state).treeDepth(), false ) );

                    state->addSubstitutionResults( subResults );
                    state->rStateType() = SUBSTITUTION_TO_APPLY;
                }
                (*state).updateValuation();
                rChildren().push_back( state );
                return 1;
            }
            else
            {
                return 0;
            }
        }
        else
        {
            return -1;
        }
    }

    /**
     * Adds a state as child to this state. The conditions are formed
     * by a condition vector plus two new conditions.
     *
     * @param _oldConditions        The conditions of this state, minus the one
     *                              used to eliminate the according variable.
     * @param _lhsCondition1        The left hand side of the first condition.
     * @param _relationCondition1   The relation symbol of the first condition.
     * @param _lhsCondition2        The left hand side of the second condition.
     * @param _relationCondition2   The relation symbol of the second condition.
     * @param _constraintVariables  The variables of the constraint used to eliminate
     *                              the according variable.
     * @param _eliminationVar       The variable, which was eliminated and now is
     *                              element of a substitution.
     * @param _subTermNum           The numerator of the term to which the variable is mapped.
     * @param _subTermDenom         The denominator of the term to which the variable is mapped.
     * @param _substitutionType     The type of the substitution we create.
     *
     * @return  1,  if a state was successfully added;
     *          0,  if a the state already exists;
     *         -1,  if the side conditions fail.
     */
    int State::addChild( const ex& _lhsCondition1,
                          const smtrat::Constraint_Relation& _relationCondition1,
                          const ex& _lhsCondition2,
                          const smtrat::Constraint_Relation& _relationCondition2,
                          const string& _eliminationVar,
                          const ex& _elimVarAsEx,
                          const ex& _subTermConstPart,
                          const ex& _subTermFactor,
                          const ex& _subTermDenom,
                          const ex& _subTermRadicand,
                          const Substitution_Type& _substitutionType,
                          const symtab& _variables,
                          const ConditionSet& _oConditions )
    {
        #ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
        #endif
        const smtrat::Constraint* cons1 = smtrat::Formula::newConstraint( _lhsCondition1, _relationCondition1, _variables );
        unsigned isCons1Consistent = (*cons1).isConsistent();
        if( isCons1Consistent != 0 )
        {
            const smtrat::Constraint* cons2 = smtrat::Formula::newConstraint( _lhsCondition2, _relationCondition2, _variables );
            unsigned isCons2Consistent = (*cons2).isConsistent();
            if( isCons2Consistent != 0 )
            {
                SqrtEx sqEx = SqrtEx( _subTermConstPart, _subTermFactor, _subTermDenom, _subTermRadicand, _variables );

                smtrat::ConstraintSet sideCond = smtrat::ConstraintSet();
                if( isCons1Consistent != 1 ) sideCond.insert( cons1 );
                if( isCons2Consistent != 1 ) sideCond.insert( cons2 );

                Substitution sub = Substitution( _eliminationVar, _elimVarAsEx, sqEx, _substitutionType, _oConditions, sideCond );
                if( !updateOCondsOfSubstitutions( sub ) )
                {
                    State* state = new State( this, sub );
                    if( !sideCond.empty() )
                    {
                        unsigned treeDepth = (*state).treeDepth();
                        std::vector<DisjunctionOfConditionConjunctions> subResults = std::vector<DisjunctionOfConditionConjunctions>();
                        subResults.push_back( DisjunctionOfConditionConjunctions() );
                        subResults.back().push_back( ConditionVector() );
                        for( auto cons = sideCond.begin(); cons != sideCond.end(); ++cons )
                        {
                            subResults.back().back().push_back( new Condition( *cons, false, _oConditions, treeDepth, false ) );
                        }
                        state->addSubstitutionResults( subResults );
                        state->rStateType() = SUBSTITUTION_TO_APPLY;
                    }
                    state->updateValuation();
                    rChildren().push_back( state );
                    return 1;
                }
                else
                {
                    return 0;
                }
            }
            else
            {
                return -1;
            }
        }
        else
        {
            return -1;
        }
    }

    /**
     *  Updates the valuation of this state.
     */
    void State::updateValuation()
    {
        if( toHighDegree() )
        {
            mValuation = 1;
        }
        else
        {
            if( !isRoot() )
            {
                mValuation = 100 * treeDepth() + 10 * substitution().valuate();
            }
            else
            {
                mValuation = 1;
            }

            if( isInconsistent() )
            {
                mValuation += 7;
            }
            else if( hasRecentlyAddedConditions() )
            {
                mValuation += 6;
            }
            else if( stateType() == TEST_CANDIDATE_TO_GENERATE && conditions().empty() )
            {
                mValuation += 5;
            }
            else
            {
                if( stateType() == SUBSTITUTION_TO_APPLY )
                {
                    mValuation += 2;
                }
                else if( stateType() == TEST_CANDIDATE_TO_GENERATE )
                {
                    mValuation += 4;
                }
                else
                {
                    mValuation += 3;
                }
            }
        }
    }

    /**
     * Passes the original conditions of the covering set of the conflicts of this state to its father.
     */
    void State::passConflictToFather( bool _includeInconsistentTestCandidates )
    {
        #ifdef VS_DEBUG_METHODS_X
        cout << __func__ << endl;
        #endif
        assert( isInconsistent() );
        /*
         * Determine a covering set of the conflict sets.
         */
        ConditionSet covSet         = ConditionSet();
        ConditionSetSetSet confSets = ConditionSetSetSet();
        ConflictSets::iterator nullConfSet = rConflictSets().find( NULL );
        if( nullConfSet != conflictSets().end() && !_includeInconsistentTestCandidates )
        {
            confSets.insert( nullConfSet->second.begin(), nullConfSet->second.end() );
        }
        else
        {
            for( ConflictSets::iterator confSet = rConflictSets().begin(); confSet != conflictSets().end(); ++confSet )
            {
                confSets.insert( confSet->second.begin(), confSet->second.end() );
            }
        }
        coveringSet( confSets, covSet, treeDepth() );

        #ifdef VS_DEBUG_METHODS_X
        cout << "*** PassConflictToFather: " << endl;
        printAlone( "   ", cout );
        cout << "***" << endl;
        cout << "*** Infeasible subset:";
        for( ConditionSet::const_iterator cond = covSet.begin(); cond != covSet.end(); ++cond )
        {
            cout << "  " << (**cond).constraint().toString();
        }
        cout << endl;
        #endif
        #ifdef VS_LOG_INFSUBSETS
        set< const smtrat::Constraint* > constraints = set< const smtrat::Constraint* >();
        for( ConditionSet::const_iterator cond = covSet.begin(); cond != covSet.end(); ++cond )
        {
            constraints.insert( (**cond).pConstraint() );
        }
        smtrat::Module::addAssumptionToCheck( constraints, false, "VSModule_IS_1" );
        #endif

        /*
         * Get the original conditions to the covering set.
         */
        ConditionSet coverSetOConds = ConditionSet();
        bool coverSetOCondsContainIndexOfFather = false;

        for( ConditionSet::iterator cond = covSet.begin(); cond != covSet.end(); ++cond )
        {
            /*
             * Add the original conditions of the condition to the conflict set.
             */
            if( !(**cond).originalConditions().empty() )
            {
                ConditionSet::iterator oCond = (**cond).originalConditions().begin();
                while( oCond != (**cond).originalConditions().end() )
                {
                    if( (**oCond).constraint().hasVariable( father().index() ) )
                    {
                        coverSetOCondsContainIndexOfFather = true;
                    }
                    coverSetOConds.insert( *oCond );
                    oCond++;
                }
            }
        }

        /*
         * If a test candidate was provided by an equation and its side condition hold always,
         * add the corresponding constraint to the conflict set. (Because we omit the other test candidates )
         */
        if( pOriginalCondition() != NULL )
        {
            /*
             * Add the corresponding original condition to the conflict set.
             */
            coverSetOConds.insert( pOriginalCondition() );

            /*
             * This original condition of course contains the index of the father,
             * as it served as test candidate provider.
             */
            coverSetOCondsContainIndexOfFather = true;
        }

        ConditionSetSet conflictSet = ConditionSetSet();
        conflictSet.insert( coverSetOConds );

        assert( !coverSetOConds.empty() );

        /*
         * Add the original conditions of the covering set as a conflict set to the father.
         */
        if( !coverSetOCondsContainIndexOfFather )
        {
            rFather().addConflictSet( NULL, conflictSet );
        }
        else
        {
            rFather().addConflictSet( pSubstitution(), conflictSet );
        }

        /*
         * Delete all children, the conflict sets and the conditions of this state.
         */
        mpConflictSets->clear();
        while( !children().empty() )
        {
            State* toDelete = rChildren().back();
            rChildren().pop_back();
            delete toDelete;
        }

        while( !conditions().empty() )
        {
            const Condition* pCond = rConditions().back();
            rConditions().pop_back();
            #ifdef SMTRAT_VS_VARIABLEBOUNDS
            mpVariableBounds->removeBound( pCond->pConstraint(), pCond );
            #endif
            delete pCond;
        }

        /*
         * Reset all necessary flags.
         */
        rHasRecentlyAddedConditions() = false;
        rTakeSubResultCombAgain()     = false;
        rFather().rMarkedAsDeleted() = false;

        bool fixedConditions = false;
        if( hasSubResultsCombination() )
        {
            if( subResultCombination().size() == 1 )
            {
                fixedConditions = substitutionResults().at( subResultCombination().back().first ).size() == 1;
            }
        }
        else
        {
            fixedConditions = true;
        }

        if( coverSetOCondsContainIndexOfFather && !fixedConditions )
        {
            rMarkedAsDeleted() = false;
            rInconsistent() = false;
            rStateType()    = COMBINE_SUBRESULTS;
        }
    }

    #ifdef SMTRAT_VS_VARIABLEBOUNDS
//    #define VS_VB_DEBUG
    /**
     *
     * @return
     */
    bool State::checkTestCandidatesForBounds()
    {
        if( mTestCandidateCheckedForBounds ) return true;
        mTestCandidateCheckedForBounds = true;
        if( variableBounds().isConflicting() )
        {
            #ifdef VS_VB_DEBUG
            cout << "case 1" << endl;
            printAlone();
            #endif
            set< const Condition* > conflictingBounds = variableBounds().getConflict();
            ConditionSet conflict = ConditionSet();
            conflict.insert( conflictingBounds.begin(), conflictingBounds.end() );
            ConditionSetSet conflicts = ConditionSetSet();
            conflicts.insert( conflict );
            addConflictSet( NULL, conflicts );
            #ifdef VS_VB_DEBUG
            printAlone( ">>>>    ", cout );
            #endif
            if( !isRoot() ) passConflictToFather();
            #ifdef VS_VB_DEBUG
            father().printAlone( ">>>>    ", cout );
            #endif
            return false;
        }
        if( !isRoot() )
        {
            if( substitution().type() == ST_MINUS_INFINITY )
            {
                if( rFather().rVariableBounds().getDoubleInterval( substitution().varAsEx() ).leftType() != DoubleInterval::INFINITY_BOUND )
                {
                    set< const Condition* > conflictingBounds = father().variableBounds().getOriginsOfBounds( ex_to<symbol>( substitution().varAsEx() ) );
                    ConditionSet conflict = ConditionSet();
                    conflict.insert( conflictingBounds.begin(), conflictingBounds.end() );
                    ConditionSetSet conflicts = ConditionSetSet();
                    conflicts.insert( conflict );
                    pFather()->addConflictSet( pSubstitution(), conflicts );
                    #ifdef VS_VB_DEBUG
                    father().printAlone( ">>>>    ", cout );
                    #endif
                    return false;
                }
            }
            else
            {
                #ifdef VS_VB_DEBUG
                cout << "case 2" << endl;
                printAlone();
                cout << substitution().term().asExpression() << "  substituted by " << endl;
                father().variableBounds().print( cout, "          " );
                cout << endl;
                #endif
                evaldoubleintervalmap intervals = rFather().rVariableBounds().getIntervalMap();
                DoubleInterval solutionSpaceConst = DoubleInterval::evaluate( substitution().term().constantPart(), intervals );
                DoubleInterval solutionSpaceFactor = DoubleInterval::evaluate( substitution().term().factor(), intervals );
                DoubleInterval solutionSpaceRadicand = DoubleInterval::evaluate( substitution().term().radicand(), intervals );
                DoubleInterval solutionSpaceSqrt = solutionSpaceRadicand.sqrt();
                DoubleInterval solutionSpaceDenom = DoubleInterval::evaluate( substitution().term().denominator(), intervals );
                DoubleInterval solutionSpace = solutionSpaceFactor * solutionSpaceSqrt;
                solutionSpace = solutionSpace + solutionSpaceConst;
                DoubleInterval divisionResultA;
                DoubleInterval divisionResultB;
                if( solutionSpace.div_ext( divisionResultA, divisionResultB, solutionSpaceDenom ) )
                {
                    symbol subVar = ex_to<symbol>( substitution().varAsEx() );
                    const DoubleInterval& subVarInterval = intervals[subVar];
                    if( substitution().type() == ST_PLUS_EPSILON && divisionResultA.leftType() != DoubleInterval::INFINITY_BOUND )
                    {
                        if( divisionResultA.rightType() == DoubleInterval::INFINITY_BOUND || divisionResultA.right() == DBL_MAX )
                        {
                            divisionResultA = DoubleInterval( divisionResultA.left(),
                                                              DoubleInterval::STRICT_BOUND,
                                                              0,
                                                              DoubleInterval::INFINITY_BOUND );
                        }
                        else
                        {
                            divisionResultA = DoubleInterval( divisionResultA.left(),
                                                              DoubleInterval::STRICT_BOUND,
                                                              std::nextafter( divisionResultA.right(), INFINITY ),
                                                              DoubleInterval::WEAK_BOUND );
                        }
                    }
                    #ifdef VS_VB_DEBUG
                    cout << " results in   ";
                    divisionResultA.dbgprint();
                    cout << "  and  ";
                    divisionResultB.dbgprint();
                    cout << endl;
                    cout << endl << "intersect first interval with  ";
                    DoubleInterval variableDomain = subVarInterval;
                    variableDomain.dbgprint();
                    cout << endl;
                    #endif
                    solutionSpace = divisionResultA.intersect( subVarInterval );
                    #ifdef VS_VB_DEBUG
                    cout << " results in   ";
                    solutionSpace.dbgprint();
                    cout << endl;
                    #endif
                    if( solutionSpace.empty() )
                    {
                        if( substitution().type() == ST_PLUS_EPSILON && divisionResultA.leftType() != DoubleInterval::INFINITY_BOUND )
                        {
                            if( divisionResultA.rightType() == DoubleInterval::INFINITY_BOUND || divisionResultA.right() == DBL_MAX )
                            {
                                divisionResultA = DoubleInterval( divisionResultA.left(),
                                                                  DoubleInterval::STRICT_BOUND,
                                                                  0,
                                                                  DoubleInterval::INFINITY_BOUND );
                            }
                            else
                            {
                                divisionResultA = DoubleInterval( divisionResultA.left(),
                                                                  DoubleInterval::STRICT_BOUND,
                                                                  std::nextafter( divisionResultA.right(), INFINITY ),
                                                                  DoubleInterval::WEAK_BOUND );
                            }
                        }
                        #ifdef VS_VB_DEBUG
                        cout << endl << "intersect first interval with  ";
                        DoubleInterval variableDomain = subVarInterval;
                        variableDomain.dbgprint();
                        cout << endl;
                        #endif
                        solutionSpace = divisionResultB.intersect( subVarInterval );
                        #ifdef VS_VB_DEBUG
                        cout << " results in   ";
                        solutionSpace.dbgprint();
                        cout << endl;
                        #endif
                        if( solutionSpace.empty() )
                        {
                            symtab vars = substitution().termVariables();
                            vars[substitution().variable()] = substitution().varAsEx();
                            set< const Condition* > conflictingBounds = father().variableBounds().getOriginsOfBounds( vars );
                            ConditionSet conflict = ConditionSet();
                            conflict.insert( conflictingBounds.begin(), conflictingBounds.end() );
                            conflict.insert( substitution().originalConditions().begin(), substitution().originalConditions().end() );
                            ConditionSetSet conflicts = ConditionSetSet();
                            conflicts.insert( conflict );
                            pFather()->addConflictSet( pSubstitution(), conflicts );
                            #ifdef VS_VB_DEBUG
                            father().printAlone( ">>>>    ", cout );
                            #endif
                            return false;
                        }
                    }
                }
                else
                {
                    if( substitution().type() == ST_PLUS_EPSILON && divisionResultA.leftType() != DoubleInterval::INFINITY_BOUND )
                    {
                        if( divisionResultA.rightType() == DoubleInterval::INFINITY_BOUND || divisionResultA.right() == DBL_MAX )
                        {
                            divisionResultA = DoubleInterval( divisionResultA.left(),
                                                              DoubleInterval::STRICT_BOUND,
                                                              0,
                                                              DoubleInterval::INFINITY_BOUND );
                        }
                        else
                        {
                            divisionResultA = DoubleInterval( divisionResultA.left(),
                                                              DoubleInterval::STRICT_BOUND,
                                                              std::nextafter( divisionResultA.right(), INFINITY ),
                                                              DoubleInterval::WEAK_BOUND );
                        }
                    }
                    #ifdef VS_VB_DEBUG
                    cout << " results in   ";
                    divisionResultA.dbgprint();
                    cout << endl;
                    cout << endl << "intersect with  ";
                    DoubleInterval variableDomain = rFather().rVariableBounds().getDoubleInterval( substitution().varAsEx() );
                    variableDomain.dbgprint();
                    cout << endl;
                    #endif
                    solutionSpace = divisionResultA.intersect( rFather().rVariableBounds().getDoubleInterval( substitution().varAsEx() ) );
                    #ifdef VS_VB_DEBUG
                    cout << " results in   ";
                    solutionSpace.dbgprint();
                    cout << endl;
                    #endif
                    if( solutionSpace.empty() )
                    {
                        symtab vars = substitution().termVariables();
                        vars[substitution().variable()] = substitution().varAsEx();
                        set< const Condition* > conflictingBounds = father().variableBounds().getOriginsOfBounds( vars );
                        ConditionSet conflict = ConditionSet();
                        conflict.insert( conflictingBounds.begin(), conflictingBounds.end() );
                        conflict.insert( substitution().originalConditions().begin(), substitution().originalConditions().end() );
                        ConditionSetSet conflicts = ConditionSetSet();
                        conflicts.insert( conflict );
                        pFather()->addConflictSet( pSubstitution(), conflicts );
                        #ifdef VS_VB_DEBUG
                        father().printAlone( ">>>>    ", cout );
                        #endif
                        return false;
                    }
                }
            }
        }
        return true;
    }
    
    /**
     * Checks whether there are no zeros for the left-hand side of the constraint of the given condition.
     * 
     * @param _condition The condition to check.
     * @return 
     */
    bool State::hasNoRootsInVariableBounds( const Condition* _condition )
    {
        symbol sym;
        _condition->constraint().variable( index(), sym );
        evaldoubleintervalmap intervals = rVariableBounds().getIntervalMap();
        DoubleInterval solutionSpace = DoubleInterval::evaluate( _condition->constraint().lhs(), intervals );
        if( !solutionSpace.contains( 0 ) )
        {
            ConditionSet origins = ConditionSet();
            origins.insert( _condition );
            smtrat::ConstraintSet constraints = smtrat::ConstraintSet();
            constraints.insert( _condition->pConstraint() );
            Substitution* sub = new Substitution( index(), ex( sym ), ST_INVALID, origins, constraints );
            symtab vars = _condition->constraint().variables();
            set< const Condition* > conflictingBounds = variableBounds().getOriginsOfBounds( vars );
            origins.insert( conflictingBounds.begin(), conflictingBounds.end() );
            ConditionSetSet conflicts = ConditionSetSet();
            conflicts.insert( origins );
            addConflictSet( sub, conflicts );
            return true;
        }
        return false;
    }
    #endif

    /**
     * Prints the conditions and the substitution of this state and all its children.
     *
     * @param _spaces   The number of spaces at the beginning of a row.
     * @param _out      The output stream, where it should print.
     */
    void State::print( const string _initiation, ostream& _out ) const
    {
        printAlone( _initiation, _out );
        _out << _initiation << "   " << "Children:" << endl;
        if( !children().empty() )
        {
            for( StateVector::const_iterator child = children().begin(); child != children().end(); ++child )
            {
                (**child).print( _initiation + "      ", _out );
            }
        }
        else
        {
            _out << _initiation << "      no" << endl;
        }
    }

    /**
     * Prints the conditions and the substitution of this state.
     *
     * @param _spaces   The number of spaces at the beginning of a row.
     * @param _out      The output stream, where it should print.
     */
    void State::printAlone( const string _initiation, ostream& _out ) const
    {
        _out << _initiation << "   State: (                     reference: " << this << endl;
        _out << _initiation << "                                valuation: " << valuation() << endl;
        _out << _initiation << "                                       ID: " << mID << endl;
        switch( stateType() )
        {
            case COMBINE_SUBRESULTS:
            {
                _out << _initiation << "                               state type: COMBINE_SUBRESULTS" << endl;
                break;
            }
            case SUBSTITUTION_TO_APPLY:
            {
                _out << _initiation << "                               state type: SUBSTITUTION_TO_APPLY" << endl;
                break;
            }
            case TEST_CANDIDATE_TO_GENERATE:
            {
                _out << _initiation << "                               state type: TEST_CANDIDATE_TO_GENERATE" << endl;
                break;
            }
            default:
            {
                _out << _initiation << "                               state type: Undefined" << endl;
            }
        }
        if( hasRecentlyAddedConditions() )
        {
            _out << _initiation << "               hasRecentlyAddedConditions: yes" << endl;
        }
        else
        {
            _out << _initiation << "               hasRecentlyAddedConditions: no" << endl;
        }
        if( isInconsistent() )
        {
            _out << _initiation << "                           isInconsistent: yes" << endl;
        }
        else
        {
            _out << _initiation << "                           isInconsistent: no" << endl;
        }
        if( conditionsSimplified() )
        {
            _out << _initiation << "                     conditionsSimplified: yes" << endl;
        }
        else
        {
            _out << _initiation << "                     conditionsSimplified: no" << endl;
        }
        if( subResultsSimplified() )
        {
            _out << _initiation << "                     subResultsSimplified: yes" << endl;
        }
        else
        {
            _out << _initiation << "                     subResultsSimplified: no" << endl;
        }
        if( takeSubResultCombAgain() )
        {
            _out << _initiation << "                   takeSubResultCombAgain: yes" << endl;
        }
        else
        {
            _out << _initiation << "                   takeSubResultCombAgain: no" << endl;
        }
        if( toHighDegree() )
        {
            _out << _initiation << "                             toHighDegree: yes" << endl;
        }
        else
        {
            _out << _initiation << "                             toHighDegree: no" << endl;
        }
        if( markedAsDeleted() )
        {
            _out << _initiation << "                          markedAsDeleted: yes" << endl;
        }
        else
        {
            _out << _initiation << "                          markedAsDeleted: no" << endl;
        }
        if( pOriginalCondition() != NULL )
        {
            _out << _initiation << "                       original condition: " << originalCondition().constraint().toString() << " ["
                 << pOriginalCondition() << "]" << endl;
        }
        _out << _initiation << "                                    index: " << index() << "     )" << endl;
        printConditions( _initiation + "   ", _out );
        if( !isRoot() )
        {
            _out << _initiation + "   " << "Substitution: ";
            substitution().print( _out );
        }
        printSubstitutionResults( _initiation + "   ", _out );
        _out << _initiation << endl;
        printSubstitutionResultCombination( _initiation + "   ", _out );
        _out << _initiation << endl;
        printConflictSets( _initiation + "   ", _out );
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        _out << _initiation << endl;
        mpVariableBounds->print( _out, _initiation );
        _out << _initiation << endl;
        #endif
    }

    /**
     * Prints the conditions of this state.
     *
     * @param _initiation   The initiation of each row to print.
     * @param _out          The output stream, where it should print.
     */
    void State::printConditions( const string _initiation, ostream& _out, bool _onlyAsConstraints ) const
    {
        _out << _initiation << "Condititons:" << endl;
        for( ConditionVector::const_iterator cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            _out << _initiation << "   ";
            if( _onlyAsConstraints )
            {
                (**cond).constraint().print();
            }
            else
            {
                (**cond).print( _out );
            }
            _out << endl;
        }
    }

    /**
     * Prints the substitution results of this state.
     *
     * @param _initiation   The initiation of each row to print.
     * @param _out          The output stream, where it should print.
     */
    void State::printSubstitutionResults( const string _initiation, ostream& _out ) const
    {
        if( hasSubstitutionResults() )
        {
            _out << _initiation << "Substitution results:" << endl;
            for( SubstitutionResults::const_iterator subResult = mpSubstitutionResults->begin(); subResult != mpSubstitutionResults->end();
                    ++subResult )
            {
                if( subResult == mpSubstitutionResults->begin() )
                    _out << _initiation << "       [ ";
                else
                    _out << _initiation << "   and [ ";
                for( SubstitutionResult::const_iterator condConjunction = subResult->begin(); condConjunction != subResult->end(); ++condConjunction )
                {
                    if( condConjunction == subResult->begin() )
                        _out << "   ( ";
                    else
                        _out << _initiation << "         or ( ";

                    for( ConditionVector::const_iterator cond = condConjunction->first.begin(); cond != condConjunction->first.end(); ++cond )
                    {
                        if( cond != condConjunction->first.begin() )
                            _out << " and ";
                        (**cond).print( _out );
                    }
                    _out << " )";
                    if( condConjunction->second )
                    {
                        _out << "_[True]  ";
                    }
                    else
                    {
                        _out << "_[False]  ";
                    }
                    SubstitutionResult::const_iterator nextCondConjunction = condConjunction;
                    ++nextCondConjunction;
                    if( nextCondConjunction != subResult->end() )
                    {
                        _out << endl;
                    }
                }
                _out << " ]" << endl;
            }
        }
    }

    /**
     * Prints the combination of substitution results used in this state.
     *
     * @param _initiation   The initiation of each row to print.
     * @param _out          The output stream, where it should print.
     */
    void State::printSubstitutionResultCombination( const string _initiation, ostream& _out ) const
    {
        if( hasSubstitutionResults() )
        {
            if( mpSubResultCombination != NULL )
            {
                _out << _initiation << "Substitution result combination:" << endl;
                for( SubResultCombination::const_iterator subResComb = mpSubResultCombination->begin(); subResComb != mpSubResultCombination->end();
                        ++subResComb )
                {
                    _out << _initiation << "   (  ";
                    for( ConditionVector::const_iterator cond = mpSubstitutionResults->at( subResComb->first ).at( subResComb->second ).first.begin();
                            cond != mpSubstitutionResults->at( subResComb->first ).at( subResComb->second ).first.end(); ++cond )
                    {
                        if( cond != mpSubstitutionResults->at( subResComb->first ).at( subResComb->second ).first.begin() )
                            _out << " and ";
                        (**cond).constraint().print( _out );
                    }
                    _out << "  )" << endl;
                }
            }
        }
    }

    /**
     * Prints the combination of substitution results, expressed in numbers, used in this state.
     *
     * @param _initiation   The initiation of each row to print.
     * @param _out          The output stream, where it should print.
     */
    void State::printSubstitutionResultCombinationAsNumbers( const string _initiation, ostream& _out ) const
    {
        if( hasSubstitutionResults() )
        {
            if( mpSubResultCombination != NULL )
            {
                _out << _initiation << "Substitution result combination:    ";
                for( SubResultCombination::const_iterator subResComb = mpSubResultCombination->begin(); subResComb != mpSubResultCombination->end();
                        ++subResComb )
                {
                    _out << "(" << subResComb->first << ", " << subResComb->second << ")  ";
                }
                _out << endl;
            }
        }
    }

    /**
     * Prints the conflict sets of this state.
     *
     * @param _initiation   The initiation of each row to print.
     * @param _out          The output stream, where it should print.
     */
    void State::printConflictSets( const string _initiation, ostream& _out ) const
    {
        _out << _initiation << "Conflict sets: " << endl;
        for( ConflictSets::const_iterator conflictSet = conflictSets().begin(); conflictSet != conflictSets().end(); ++conflictSet )
        {
            if( conflictSet->first != NULL )
            {
                conflictSet->first->print( true, true, _out, _initiation + "    " );
            }
            else
            {
                _out << _initiation << "    NULL" << endl;
            }
            for( ConditionSetSetSet::const_iterator condSetSet = conflictSet->second.begin(); condSetSet != conflictSet->second.end(); ++condSetSet )
            {
                ConditionSetSet::const_iterator condSet = condSetSet->begin();
                if( condSet != condSetSet->end() )
                {
                    _out << _initiation << "       {";
                    ConditionSet::const_iterator cond = (*condSet).begin();
                    if( cond != (*condSet).end() )
                    {
                        _out << " { [";
                        (**cond).constraint().print( _out );
                        _out << "]" << "_" << (**cond).valuation();
                        ++cond;
                        while( cond != (*condSet).end() )
                        {
                            _out << ", [";
                            (**cond).constraint().print( _out );
                            _out << "]" << "_" << (**cond).valuation();
                            ++cond;
                        }
                        _out << " }";
                    }
                    else
                    {
                        _out << " {}";
                    }
                    ++condSet;
                    while( condSet != condSetSet->end() )
                    {
                        _out << "," << endl;
                        _out << _initiation << "        ";
                        ConditionSet::const_iterator cond = (*condSet).begin();
                        if( cond != (*condSet).end() )
                        {
                            _out << " { [";
                            (**cond).constraint().print( _out );
                            _out << "]" << "_" << (**cond).valuation();
                            ++cond;
                            while( cond != (*condSet).end() )
                            {
                                _out << ", [";
                                (**cond).constraint().print( _out );
                                _out << "]" << "_" << (**cond).valuation();
                                ++cond;
                            }
                            _out << " }";
                        }
                        else
                        {
                            _out << " {}";
                        }
                        ++condSet;
                    }
                    _out << " }" << endl;
                }
                else
                {
                    _out << _initiation << "       {}" << endl;
                }
            }
        }
    }

    /**
     * Finds a covering set of a vector of sets of sets due to some heuristics.
     *
     * @param _conflictSets The vector of sets of sets, for which the method finds all minimum covering sets.
     * @param _minCovSet    The found mininum covering set.
     *
     * @return The greatest level, where a condition of the covering set has been created.
     */
    unsigned State::coveringSet( const ConditionSetSetSet& _conflictSets, ConditionSet& _coveringSet, const unsigned _currentTreeDepth )
    {
        /*
         * Greatest tree depth of the original conditions of the conditions in the covering set.
         */
        unsigned greatestTreeDepth = 0;
        for( ConditionSetSetSet::const_iterator conflictSet = _conflictSets.begin(); conflictSet != _conflictSets.end(); ++conflictSet )
        {
            if( !conflictSet->empty() )
            {
                /*
                 * Greatest tree depth of the original conditions of the conditions in the
                 * currently best set of conditions in this conflict set.
                 */
                unsigned greatestTreeDepthConflictSet = 0;

                /*
                 * The number of conditions in the currently best set of conditions, which are
                 * not covered of the so far created covering set.
                 */
                unsigned                        numUncovCondsConflictSet = 0;
                ConditionSetSet::const_iterator bestConditionSet         = conflictSet->begin();
                for( ConditionSetSet::const_iterator conditionSet = conflictSet->begin(); conditionSet != conflictSet->end(); ++conditionSet )
                {
                    unsigned numUncovCondsCondSet     = 0;
                    unsigned greatestTreeDepthCondSet = 0;
                    bool     justEmptyOConds          = true;
                    for( ConditionSet::const_iterator condition = conditionSet->begin(); condition != conditionSet->end(); ++condition )
                    {
                        if( _coveringSet.find( *condition ) == _coveringSet.end() )
                        {
                            numUncovCondsCondSet++;
                        }
                        for( ConditionSet::const_iterator oCond = (**condition).originalConditions().begin();
                                oCond != (**condition).originalConditions().end(); ++oCond )
                        {
                            justEmptyOConds = false;
                            if( (**oCond).valuation() > greatestTreeDepthCondSet )
                            {
                                greatestTreeDepthCondSet = (**oCond).valuation();
                            }
                        }
                    }
                    if( justEmptyOConds )
                    {
                        greatestTreeDepthCondSet = _currentTreeDepth - 1;
                    }
                    if( conditionSet == conflictSet->begin() || (greatestTreeDepthCondSet < greatestTreeDepthConflictSet)
                            || ((greatestTreeDepthCondSet == greatestTreeDepthConflictSet && numUncovCondsCondSet < numUncovCondsConflictSet)) )
                    {
                        bestConditionSet             = conditionSet;
                        greatestTreeDepthConflictSet = greatestTreeDepthCondSet;
                        numUncovCondsConflictSet     = numUncovCondsCondSet;
                    }
                }
                if( greatestTreeDepthConflictSet > greatestTreeDepth )
                {
                    greatestTreeDepth = greatestTreeDepthConflictSet;
                }
                _coveringSet.insert( bestConditionSet->begin(), bestConditionSet->end() );
            }
        }
        return greatestTreeDepth;
    }

}    // end namspace vs

