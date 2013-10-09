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
 * @version 2013-06-20
 */

#include <cmath>
#include <float.h>
#include "State.h"
#include "../../Module.h"

//#define VS_DEBUG_VARIABLE_VALUATIONS
//#define VS_DEBUG_VARIABLE_BOUNDS
//#define VS_DEBUG_LOCAL_CONFLICT_SEARCH
//#define VS_DEBUG_ROOTS_CHECK
//#define VS_LOG_INFSUBSETS

using namespace std;
using namespace GiNaC;
using namespace GiNaCRA;

namespace vs
{
    State::State( bool _withVariableBounds ):
        mConditionsSimplified( false ),
        mHasChildrenToInsert( false ),
        mHasRecentlyAddedConditions( false ),
        mInconsistent( false ),
        mMarkedAsDeleted( false ),
        mSubResultsSimplified( false ),
        mTakeSubResultCombAgain( false ),
        mTestCandidateCheckedForBounds( false ),
        mTestCandidateInBoundsCreated( false ),
        mToHighDegree( false ),
        mTryToRefreshIndex( false ),
        mBackendCallValuation( 0 ),
        mID( 0 ),
        mValuation( 0 ),
        mType( TEST_CANDIDATE_TO_GENERATE ),
        mpIndex( new string( "" ) ),
        mpOriginalCondition( NULL ),
        mpFather( NULL ),
        mpSubstitution( NULL ),
        mpSubstitutionResults( NULL ),
        mpSubResultCombination( NULL ),
        mpConditions( new ConditionList() ),
        mpConflictSets( new ConflictSets() ),
        mpChildren( new StateVector() ),
        mpTooHighDegreeConditions( new set< const Condition* >() ),
        mpVariableBounds( _withVariableBounds ? new VariableBounds() : NULL )
    {}

    State::State( State* const _father, const Substitution& _substitution, bool _withVariableBounds ):
        mConditionsSimplified( false ),
        mHasChildrenToInsert( false ),
        mHasRecentlyAddedConditions( false ),
        mInconsistent( false ),
        mMarkedAsDeleted( false ),
        mSubResultsSimplified( false ),
        mTakeSubResultCombAgain( false ),
        mTestCandidateCheckedForBounds( false ),
        mTestCandidateInBoundsCreated( false ),
        mToHighDegree( false ),
        mTryToRefreshIndex( false ),
        mBackendCallValuation( 0 ),
        mID( 0 ),
        mValuation( 0 ),
        mType( SUBSTITUTION_TO_APPLY ),
        mpIndex( new string( "" ) ),
        mpOriginalCondition( NULL ),
        mpFather( _father ),
        mpSubstitution( new Substitution( _substitution ) ),
        mpSubstitutionResults( NULL ),
        mpSubResultCombination( NULL ),
        mpConditions( new ConditionList() ),
        mpConflictSets( new ConflictSets() ),
        mpChildren( new StateVector() ),
        mpTooHighDegreeConditions( new set< const Condition* >() ),
        mpVariableBounds( _withVariableBounds ? new VariableBounds() : NULL )
    {}

    State::~State()
    {
        mpTooHighDegreeConditions->clear();
        delete mpTooHighDegreeConditions;
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
            if( mpVariableBounds != NULL )
                mpVariableBounds->removeBound( pCond->pConstraint(), pCond );
            delete pCond;
            pCond = NULL;
        }
        if( mpVariableBounds != NULL )
            delete mpVariableBounds;
        delete mpConditions;
        if( mpSubstitution != NULL )
            delete mpSubstitution;
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
                        rpCond = NULL;
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
        ConditionList::const_iterator cond = conditions().begin();
        while( cond != conditions().end() )
        {
            if( substitutionApplicable( (**cond).constraint() ) )
                return true;
            ++cond;
        }
        return false;
    }

    /**
     * Checks if the substitution of this state can be applied to the given
     * constraint.
     *
     * @param _constraint   The constraint, for which we want to know, if the substitution
     *                      is applicable.
     *
     * @return  True,   if the substitution can be applied.
     *          False,  else.
     */
    bool State::substitutionApplicable( const smtrat::Constraint& _constraint ) const
    {
        if( !isRoot() )
            if( _constraint.variables().find( substitution().variable() ) != _constraint.variables().end() )
                return true;
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
        ConditionList::const_iterator cond = conditions().begin();
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
     * Checks whether a child exists, which is not yet marked as inconsistent.
     * 
     * @return True, if there exists such a child.
     */
    bool State::hasOnlyInconsistentChildren() const
    {
        StateVector::const_iterator child = children().begin();
        while( child != children().end() )
        {
            if( (*child)->isInconsistent() )
                ++child;
            else
                return false;
        }
        return true;
    }

    /**
     * Checks whether the given variable occurs in a equation.
     *
     * @return  true,   if the given variable occurs in a equation;
     *          false,  otherwise.
     */
    bool State::occursInEquation( const string& _variableName ) const
    {
        for( ConditionList::const_iterator cond = conditions().begin(); cond != conditions().end(); ++cond )
            if( (*cond)->constraint().relation() == smtrat::CR_EQ && (*cond)->constraint().hasVariable( _variableName ) )
                return true;
        return false;
    }

    /**
     * Checks whether there exist more than one test candidate, which has still not been checked.
     *
     * @return  true, if there exist more than one test candidate, which has still not been checked;
     *          false, otherwise.
     */
    bool State::hasFurtherUncheckedTestCandidates() const
    {
        if( children().size() > 1 )
            return true;
        else
        {
            for( ConditionList::const_iterator cond = conditions().begin(); cond != conditions().end(); ++cond )
                if( !(**cond).flag() )
                    return true;
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
        for( auto cond = conditions().begin(); cond != conditions().end(); ++cond )
            for( auto var = (**cond).constraint().variables().begin(); var != (**cond).constraint().variables().end(); ++var )
                _variables.insert( (*var).first );
    }

    /**
     * Determines the number of nodes in the tree with this state as root.
     *
     * @return The number of nodes in the tree with this state as root.
     */
    unsigned State::numberOfNodes() const
    {
        unsigned result = 1;
        for( auto child = children().begin(); child != children().end(); ++child )
            result += (**child).numberOfNodes();
        return result;
    }

    /**
     * Checks the substitution result combination vector.
     *
     * @return  true,   if there is an error in the substitution result combination vector;
     *          false,  otherwise.
     */
    bool State::checkSubResultsCombs() const
    {
        if( hasSubstitutionResults() )
        {
            if( hasSubResultsCombination() )
            {
                for( auto subResComb = subResultCombination().begin(); subResComb != subResultCombination().end(); ++subResComb )
                {
                    if( subResComb->first < 0 || subResComb->first >= substitutionResults().size() )
                        return true;
                    else
                        if( subResComb->second < 0 || subResComb->second >= mpSubstitutionResults->at( subResComb->first ).size()
                            || mpSubstitutionResults->at( subResComb->first ).size() == 0 )
                        {
                            return true;
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
            currentDT = (*currentDT).pFather();
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
        _unfinAnt = this;
        while( !_unfinAnt->isRoot() )
        {
            if( _unfinAnt->unfinished() )
                return true;
            _unfinAnt = _unfinAnt->pFather();
        }
        return _unfinAnt->unfinished();
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
    bool State::bestCondition( const Condition*& _bestCondition, const unsigned _numberOfAllVariables, bool _preferEquation )
    {
        ConditionList::iterator cond = rConditions().begin();
        if( cond == conditions().end() )
            return false;
        assert( index() != "" );
        // Find the best condition.
        _bestCondition = *cond;
        ++cond;
        double bestConditionValuation    = _bestCondition->valuate( index(), _numberOfAllVariables, true, _preferEquation );
        double currentConditionValuation = 0;
        while( cond != conditions().end() )
        {
            if( !(**cond).flag() )
            {
                if( (*_bestCondition).flag() )
                {
                    _bestCondition         = *cond;
                    bestConditionValuation = _bestCondition->valuate( index(), _numberOfAllVariables, true, _preferEquation );
                }
                else
                {
                    currentConditionValuation = (**cond).valuate( index(), _numberOfAllVariables, true, _preferEquation );
                    if( currentConditionValuation != 0 && ( currentConditionValuation < bestConditionValuation || bestConditionValuation == 0 ) )
                    {
                        _bestCondition         = *cond;
                        bestConditionValuation = currentConditionValuation;
                    }
                }
            }
            ++cond;
        }
        // If all constraints were considered to yield test candidates, return false
        // which means that there is no condition in general. Otherwise return true.
        return !(*_bestCondition).flag();
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
    ConditionList::iterator State::constraintExists( const smtrat::Constraint& _constraint )
    {
        for( ConditionList::iterator cond = rConditions().begin(); cond != conditions().end(); ++cond )
            if( (**cond).constraint() == _constraint )
                return cond;
        return rConditions().end();
    }

    /**
     * Cleans up all conditions in this state according to comparison between the corresponding constraints.
     */
    void State::simplify()
    {
        if( !subResultsSimplified() )
        {
            if( hasSubstitutionResults() )
            {
                // If these conjunction together are consistent, simplify all conjunctions of
                // conditions in the remaining substitution results being disjunctions.
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
                        ConditionSetSet conflictingConditionPairs = ConditionSetSet();
                        if( !simplify( condConjunction->first, conflictingConditionPairs ) )
                        {
                            while( !condConjunction->first.empty() )
                            {
                                const Condition* rpCond = condConjunction->first.back();
                                condConjunction->first.pop_back();
                                delete rpCond;
                                rpCond = NULL;
                            }
                            condConjunction = subResult->erase( condConjunction );
                        }
                        else
                        {
                            if( condConjunction->first.empty() )
                                containsEmptyCase = true;
                            ++condConjunction;
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
                                    subResComb = rSubResultCombination().erase( subResComb );
                                else if( subResComb->first > subResultIndex )
                                {
                                    --(subResComb->first);
                                    ++subResComb;
                                }
                                else
                                    ++subResComb;
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
                                rpCond = NULL;
                            }
                            subResult->pop_back();
                        }
                        subResult = mpSubstitutionResults->erase( subResult );
                        if( fixedPosWasEndBefore ) fixedConditions = mpSubstitutionResults->end();
                        if( mpSubResultCombination != NULL )
                        {
                            if( mpSubResultCombination->size() > 0 )
                                mTakeSubResultCombAgain = true;
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
                                            subResComb = rSubResultCombination().erase( subResComb );
                                        else if( subResComb->first > subResultIndex )
                                        {
                                            --(subResComb->first);
                                            ++subResComb;
                                        }
                                        else
                                            ++subResComb;
                                    }
                                }
                                subResult = mpSubstitutionResults->erase( subResult );
                                if( mpSubResultCombination != NULL )
                                {
                                    if( mpSubResultCombination->size() > 0 )
                                        mTakeSubResultCombAgain = true;
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
                // If the state is already inconsistent update obvious conflicts.
                if( isInconsistent() && fixedConditions != mpSubstitutionResults->end() )
                {
                    ConditionSetSet conflictingConditionPairs = ConditionSetSet();
                    if( !simplify( fixedConditions->back().first, conflictingConditionPairs ) )
                        addConflicts( NULL, conflictingConditionPairs );
                }
            }
            mSubResultsSimplified = true;
        }
        // Simplify the condition vector.
        if( !conditionsSimplified() )
        {
            ConditionSetSet conflictingConditionPairs = ConditionSetSet();
            if( !simplify( rConditions(), conflictingConditionPairs, true ) )
            {
                addConflictSet( NULL, conflictingConditionPairs );
                rInconsistent() = true;
            }
            mConditionsSimplified = true;
        }
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
    bool State::simplify( ConditionList& _conditionVectorToSimplify, ConditionSetSet& _conflictSet, bool _stateConditions )
    {
        if( _conditionVectorToSimplify.size() > 1 )
        {
            set<const Condition*> redundantConditionSet = set<const Condition*>();
            ConditionList::const_iterator iterA = _conditionVectorToSimplify.begin();
            // Check all condition combinations.
            while( iterA != _conditionVectorToSimplify.end() )
            {
                ConditionList::const_iterator iterB = iterA;
                ++iterB;
                while( iterB != _conditionVectorToSimplify.end() )
                {
                    const Condition* condA = *iterA;
                    const Condition* condB = *iterB;
                    signed strongProp = smtrat::Constraint::compare( condA->pConstraint(), condB->pConstraint() );
                    // If the two conditions have the same solution space.
                    if( strongProp == 2 )
                    {
                        // Choose original conditions.
                        if( !condA->originalConditions().empty() &&!condB->originalConditions().empty() )
                        {
                            // If we have to choose which original conditions to take, choose those, which have been created earlier.
                            if( condB->valuation() < condA->valuation() )
                            {
                                *condA->pOriginalConditions() = ConditionSet( condB->originalConditions() );
                                condA->rValuation()          = condB->valuation();
                            }
                        }
                        else
                            condA->pOriginalConditions()->insert( condB->originalConditions().begin(), condB->originalConditions().end() );
                        redundantConditionSet.insert( condB );
                    }
                    // If cond1's solution space is a subset of the solution space of cond2.
                    else if( strongProp == 1 )
                        redundantConditionSet.insert( condB );
                    // If it is easy to give a condition whose solution space is the intersection of the solution spaces of cond1 and cond2.
                    else if( strongProp == -3 )
                    {
                        const smtrat::Constraint& constraintA = condA->constraint();
                        const smtrat::Constraint& constraintB = condB->constraint();
                        if( (constraintA.relation() == smtrat::CR_GEQ && constraintB.relation() == smtrat::CR_GEQ)
                                || (constraintA.relation() == smtrat::CR_GEQ && constraintB.relation() == smtrat::CR_LEQ)
                                || (constraintA.relation() == smtrat::CR_LEQ && constraintB.relation() == smtrat::CR_GEQ)
                                || (constraintA.relation() == smtrat::CR_LEQ && constraintB.relation() == smtrat::CR_LEQ) )
                        {
                            const smtrat::Constraint* nConstraint = smtrat::Formula::newConstraint( constraintB.lhs(), smtrat::CR_EQ, constraintB.variables() );
                            if( _stateConditions )
                            {
                                ConditionSet oConds = condB->originalConditions();
                                oConds.insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                                addCondition( nConstraint, oConds, condB->valuation(), true );
                            }
                            else
                            {
                                const Condition* cond = new Condition( nConstraint, condB->valuation(), condB->flag(), condB->originalConditions(), true );
                                cond->pOriginalConditions()->insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                                _conditionVectorToSimplify.push_back( cond );
                            }
                            redundantConditionSet.insert( condA );
                            redundantConditionSet.insert( condB );
                            if( nConstraint->isConsistent() == 0 )
                            {
                                ConditionSet condSet = ConditionSet();
                                condSet.insert( condA );
                                condSet.insert( condB );
                                _conflictSet.insert( condSet );
                            }
                        }
                        else if( (constraintA.relation() == smtrat::CR_NEQ && constraintB.relation() == smtrat::CR_GEQ) )
                        {
                            const smtrat::Constraint* nConstraint = smtrat::Formula::newConstraint( constraintB.lhs(), smtrat::CR_GREATER, constraintB.variables() );
                            if( _stateConditions )
                            {
                                ConditionSet oConds = condB->originalConditions();
                                oConds.insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                                addCondition( nConstraint, oConds, condB->valuation(), true );
                            }
                            else
                            {
                                const Condition* cond = new Condition( nConstraint, condB->valuation(), condB->flag(), condB->originalConditions(), true );
                                cond->pOriginalConditions()->insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                                _conditionVectorToSimplify.push_back( cond );
                            }
                            redundantConditionSet.insert( condA );
                            redundantConditionSet.insert( condB );
                            if( nConstraint->isConsistent() == 0 )
                            {
                                ConditionSet condSet = ConditionSet();
                                condSet.insert( condA );
                                condSet.insert( condB );
                                _conflictSet.insert( condSet );
                            }
                        }
                        else if( (constraintA.relation() == smtrat::CR_GEQ && constraintB.relation() == smtrat::CR_NEQ) )
                        {
                            const smtrat::Constraint* nConstraint = smtrat::Formula::newConstraint( constraintA.lhs(), smtrat::CR_GREATER, constraintA.variables() );
                            if( _stateConditions )
                            {
                                ConditionSet oConds = condB->originalConditions();
                                oConds.insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                                addCondition( nConstraint, oConds, condA->valuation(), true );
                            }
                            else
                            {
                                const Condition* cond = new Condition( nConstraint, condA->valuation(), condA->flag(), condA->originalConditions(), true );
                                cond->pOriginalConditions()->insert( condB->originalConditions().begin(), condB->originalConditions().end() );
                                _conditionVectorToSimplify.push_back( cond );
                            }
                            redundantConditionSet.insert( condA );
                            redundantConditionSet.insert( condB );
                            if( nConstraint->isConsistent() == 0 )
                            {
                                ConditionSet condSet = ConditionSet();
                                condSet.insert( condA );
                                condSet.insert( condB );
                                _conflictSet.insert( condSet );
                            }
                        }
                        else if( (constraintA.relation() == smtrat::CR_NEQ && constraintB.relation() == smtrat::CR_LEQ) )
                        {
                            const smtrat::Constraint* nConstraint = smtrat::Formula::newConstraint( constraintB.lhs(), smtrat::CR_LESS, constraintB.variables() );
                            if( _stateConditions )
                            {
                                ConditionSet oConds = condB->originalConditions();
                                oConds.insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                                addCondition( nConstraint, oConds, condB->valuation(), true );
                            }
                            else
                            {
                                const Condition* cond = new Condition( nConstraint, condB->valuation(), condB->flag(), condB->originalConditions(), true );
                                cond->pOriginalConditions()->insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                                _conditionVectorToSimplify.push_back( cond );
                            }
                            redundantConditionSet.insert( condA );
                            redundantConditionSet.insert( condB );
                            if( nConstraint->isConsistent() == 0 )
                            {
                                ConditionSet condSet = ConditionSet();
                                condSet.insert( condA );
                                condSet.insert( condB );
                                _conflictSet.insert( condSet );
                            }
                        }
                        else if( (constraintA.relation() == smtrat::CR_LEQ && constraintB.relation() == smtrat::CR_NEQ) )
                        {
                            const smtrat::Constraint* nConstraint = smtrat::Formula::newConstraint( constraintA.lhs(), smtrat::CR_LESS, constraintA.variables() );
                            if( _stateConditions )
                            {
                                ConditionSet oConds = condB->originalConditions();
                                oConds.insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                                addCondition( nConstraint, oConds, condA->valuation(), true );
                            }
                            else
                            {
                                const Condition* cond = new Condition( nConstraint, condA->valuation(), condA->flag(), condA->originalConditions(), true );
                                cond->pOriginalConditions()->insert( condB->originalConditions().begin(), condB->originalConditions().end() );
                                _conditionVectorToSimplify.push_back( cond );
                            }
                            redundantConditionSet.insert( condA );
                            redundantConditionSet.insert( condB );
                            if( nConstraint->isConsistent() == 0 )
                            {
                                ConditionSet condSet = ConditionSet();
                                condSet.insert( condA );
                                condSet.insert( condB );
                                _conflictSet.insert( condSet );
                            }
                        }
                        else
                            assert( false );
                    }
                    // If cond1's solution space is a superset of the solution space of cond2.
                    else if( strongProp == -1 )
                        redundantConditionSet.insert( condA );
                    // If it is easy to decide that cond1 and cond2 are conflicting.
                    else if( strongProp == -2 || strongProp == -4 )
                    {
                        ConditionSet condSet = ConditionSet();
                        condSet.insert( condA );
                        condSet.insert( condB );
                        _conflictSet.insert( condSet );
                    }
                    ++iterB;
                }
                ++iterA;
            }

            // Delete the conflicting conditions from redundant conditions.
            ConditionSetSet::iterator condSet = _conflictSet.begin();
            while( condSet != _conflictSet.end() )
            {
                ConditionSet::iterator cond = condSet->begin();
                while( cond != condSet->end() )
                    redundantConditionSet.erase( *cond++ );
                ++condSet;
            }
            if( _stateConditions )
                deleteConditions( redundantConditionSet );
            else
            {
                // Delete the redundant conditions of the vector of conditions to simplify.
                ConditionList::iterator cond = _conditionVectorToSimplify.begin();
                while( cond != _conditionVectorToSimplify.end() )
                {
                    if( redundantConditionSet.find( *cond ) != redundantConditionSet.end() )
                        cond = _conditionVectorToSimplify.erase( cond );
                    else
                        ++cond;
                }
            }
            while( !redundantConditionSet.empty() )
            {
                const Condition* toDelete = *redundantConditionSet.begin();
                redundantConditionSet.erase( redundantConditionSet.begin() );
                delete toDelete;
                toDelete = NULL;
            }
        }
        return _conflictSet.empty();
    }

    /**
     * Sets the index of this state.
     *
     * @param _index The string to which the index should be set.
     */
    void State::setIndex( const string& _index )
    {
        *mpIndex = _index;
        initConditionFlags();
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
        ConflictSets::iterator iter = mpConflictSets->find( _substitution );
        if( iter != mpConflictSets->end() )
            iter->second.insert( _condSetSet );
        else
        {
            ConditionSetSetSet condSetSetSet = ConditionSetSetSet();
            condSetSetSet.insert( _condSetSet );
            mpConflictSets->insert( pair<const Substitution* const , ConditionSetSetSet>( _substitution, condSetSetSet ) );
        }
        if( _substitution == NULL )
            rInconsistent() = true;
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

    /**
     * Clears the conflict sets.
     */
    void State::resetConflictSets()
    {
        if( !mpConflictSets->empty() )
        {
            auto conflictSet = mpConflictSets->begin();
            if( conflictSet->first == NULL )
                ++conflictSet;
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
        // For each disjunction add a substitution result to the substitution results of this state.
        if( mpSubstitutionResults == NULL )
            mpSubstitutionResults = new SubstitutionResults();
        for( auto disjunction = _disjunctionsOfCondConj.begin(); disjunction != _disjunctionsOfCondConj.end(); ++disjunction )
        {
            mpSubstitutionResults->push_back( SubstitutionResult() );
            for( auto conjunction = disjunction->begin(); conjunction != disjunction->end(); ++conjunction )
                mpSubstitutionResults->back().push_back( pair<ConditionList, bool>( *conjunction, false ) );
        }
        // Mark this state as not yet simplified.
        mSubResultsSimplified = false;
        mToHighDegree         = false;
        mMarkedAsDeleted      = false;
        mType                 = COMBINE_SUBRESULTS;
    }

    /**
     * Extends the currently considered combination of conjunctions in the substitution results.
     */
    bool State::extendSubResultCombination()
    {
        assert( subResultsSimplified() );
        if( mpSubResultCombination == NULL )
            mpSubResultCombination = new SubResultCombination();
        if( mpSubResultCombination->size() < mpSubstitutionResults->size() )
        {
            unsigned bestSubResultIndex          = 0;
            bool     notConsideredSubResultFound = false;
            unsigned subResultIndex              = 0;
            while( subResultIndex < mpSubstitutionResults->size() )
            {
                // Set all flags of conjunctions of conditions in the substitution result to false.
                SubstitutionResult::iterator condConj = mpSubstitutionResults->at( subResultIndex ).begin();
                while( condConj != mpSubstitutionResults->at( subResultIndex ).end() )
                {
                    condConj->second = false;
                    ++condConj;
                }
                // Check whether the sub result has not yet been considered.
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
                        // We have already a currently best substitution result and check if
                        // it is better than the substitution result we consider now.
                        unsigned subResultSize = mpSubstitutionResults->at( subResultIndex ).size();
                        assert( subResultSize > 0 );
                        if( subResultSize < mpSubstitutionResults->at( bestSubResultIndex ).size() )
                            bestSubResultIndex = subResultIndex;
                    }
                    else
                    {
                        // This is the first not yet considered substitution result, so add take it as the currently best one.
                        assert( mpSubstitutionResults->at( subResultIndex ).size() > 0 );
                        bestSubResultIndex          = subResultIndex;
                        notConsideredSubResultFound = true;
                    }
                }
                ++subResultIndex;
            }
            // Add the found substitution result to the substitution result combinations.
            mpSubResultCombination->push_back( pair<unsigned, unsigned>( bestSubResultIndex, 0 ) );
            return true;
        }
        else
            return false;
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
        assert( type() == COMBINE_SUBRESULTS );
        if( !hasSubResultsCombination() )
        {
            extendSubResultCombination();
            return true;
        }
        else
        {
            assert( mpSubResultCombination->size() <= mpSubstitutionResults->size() );
            if( takeSubResultCombAgain() )
                mTakeSubResultCombAgain = false;
            else
            {
                SubResultCombination::reverse_iterator rIter = mpSubResultCombination->rbegin();
                while( rIter != mpSubResultCombination->rend() )
                {
                    // Take the next conjunction of conditions of the considered substitution result, which
                    // has the flag false.
                    mpSubstitutionResults->at( rIter->first ).at( rIter->second ).second = true;
                    while( rIter->second < mpSubstitutionResults->at( rIter->first ).size() - 1
                            && mpSubstitutionResults->at( rIter->first ).at( rIter->second ).second )
                    {
                        ++(rIter->second);
                    }
                    // If it has already been the last conjunction of conditions of the considered substitution result.
                    if( rIter->second == mpSubstitutionResults->at( rIter->first ).size() - 1
                            && mpSubstitutionResults->at( rIter->first ).at( rIter->second ).second )
                    {
                        // Check if we already have reached the first substitution result.
                        SubResultCombination::const_reverse_iterator rIterTemp = rIter;
                        ++rIterTemp;
                        // If we currently consider the first substitution result, return false,
                        // which means, that there is no other combination to consider.
                        if( rIterTemp == mpSubResultCombination->rend() )
                            return false;
                        // Otherwise, go back the first conjunction of conditions of the currently considered substitution
                        // result and try to go to the next conjunction of  conditions in the next substitution result.
                        else
                        {
                            for( auto condConj = mpSubstitutionResults->at( rIter->first ).begin();
                                    condConj != mpSubstitutionResults->at( rIter->first ).end(); ++condConj )
                            {
                                condConj->second = false;
                            }
                            rIter->second = 0;
                        }
                    }
                    // Otherwise we found a valid new combination of condition conjunctions.
                    else
                        return true;
                    ++rIter;
                }
            }
            // A valid new combination of substitution results is established.
            return true;
        }
    }

    /**
     * Gets the current substitution result combination as condition vector.
     *
     * @return The current substitution result combination as condition vector.
     */
    const ConditionList State::getCurrentSubresultCombination() const
    {
        ConditionList currentSubresultCombination = ConditionList();
        SubResultCombination::const_iterator iter = mpSubResultCombination->begin();
        while( iter != mpSubResultCombination->end() )
        {
            for( auto cond = mpSubstitutionResults->at( iter->first ).at( iter->second ).first.begin();
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
     * 
     * @return True, if there has been a change in the currently considered condition vector.
     *          False, otherwise.
     */
    bool State::refreshConditions()
    {
        assert( type() == COMBINE_SUBRESULTS );
        bool conditionsChanged = false;
        if( !mpSubstitutionResults->empty() )
        {
            // Get the conditions of the currently considered combination of substitution results.
            ConditionList newCombination = getCurrentSubresultCombination();
            // Simplify the conditions already here, to avoid unnecessarily adding and deleting conditions.
            ConditionList redundantConditions       = ConditionList();
            ConditionSetSet conflictingConditionPairs = ConditionSetSet();
            if( !simplify( newCombination, conflictingConditionPairs ) )
                rInconsistent() = true;
            // Delete the conditions of this combination, which do already occur in the considered conditions of this state.
            set<const Condition*> condsToDelete = set<const Condition*>();
            ConditionList::iterator cond = rConditions().begin();
            while( cond != conditions().end() )
            {
                // Check if the condition occurs in the new combination. If so, delete
                // the corresponding condition in the new combination.
                bool                      condOccursInNewConds = false;
                ConditionList::iterator newCond              = newCombination.begin();
                while( newCond != newCombination.end() )
                {
                    if( (**cond).constraint() == (**newCond).constraint() )
                    {
                        // Choose original conditions.
                        if( !(**cond).originalConditions().empty() &&!(**newCond).originalConditions().empty() )
                        {
                            // If we have to choose which original conditions to take, choose those, which have been created earlier.
                            if( (**newCond).valuation() < (**cond).valuation() )
                            {
                                *(**cond).pOriginalConditions() = ConditionSet( (**newCond).originalConditions() );
                                (**cond).rValuation()          = (**newCond).valuation();
                            }
                        }
                        else
                            (**cond).pOriginalConditions()->insert( (**newCond).originalConditions().begin(), (**newCond).originalConditions().end() );
                        const Condition* pCond = *newCond;
                        newCombination.erase( newCond );
                        delete pCond;
                        pCond = NULL;
                        condOccursInNewConds = true;
                        break;
                    }
                    else
                        ++newCond;
                }
                // Remember the condition not occurring in the current combination.
                if( !condOccursInNewConds )
                {
                    condsToDelete.insert( *cond );
                    conditionsChanged = true;
                }
                ++cond;
            }
            if( !newCombination.empty() )
                conditionsChanged = true;
            // Delete the conditions, which do not occur in the current combination.
            if( !condsToDelete.empty() )
            {
                deleteConditions( condsToDelete );
                while( !condsToDelete.empty() )
                {
                    const vs::Condition* toDelete = *condsToDelete.begin();
                    condsToDelete.erase( condsToDelete.begin() );
                    delete toDelete;
                    toDelete = NULL;
                }
            }
            // Add the remaining conditions of the current combination to the conditions this state considers.
            for( ConditionList::const_iterator newCond = newCombination.begin(); newCond != newCombination.end(); ++newCond )
                addCondition( (**newCond).pConstraint(), (**newCond).originalConditions(), (**newCond).valuation(), true );
            while( !newCombination.empty() )
            {
                const Condition*& rpCond = newCombination.back();
                newCombination.pop_back();
                delete rpCond;
                rpCond = NULL;
            }
        }
        mType = TEST_CANDIDATE_TO_GENERATE;
        if( conditionsChanged )
        {
            mConditionsSimplified = false;
            mTryToRefreshIndex    = true;
            return true;
        }
        else
            return false;
    }

    /**
     * Sets all flags of the conditions to true, if it contains the variable given by the states index.
     */
    void State::initConditionFlags()
    {
        for( ConditionList::iterator cond = rConditions().begin(); cond != conditions().end(); ++cond )
            (**cond).rFlag() = !(**cond).constraint().hasVariable( index() );
    }

    /**
     * Sets, if it has not already happened, the index of the state to the name of the
     * most adequate variable. Which variable is taken depends on heuristics.
     *
     * @param   _allVariables   All globally known variables.
     */
    bool State::initIndex( const symtab& _allVariables, bool _preferEquation )
    {
        mTryToRefreshIndex = false;
        if( conditions().empty() )
            return false;
        map<string, multiset<double> > varVals = map<string, multiset<double> >();
        for( symtab::const_iterator var = _allVariables.begin(); var != _allVariables.end(); ++var )
            varVals.insert( pair<string, multiset<double> >( var->first, multiset<double>() ) );
        // Find for each variable the highest valuation of all conditions' constraints.
        for( ConditionList::const_iterator cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            // Check for all variables their valuation for the given constraint.
            for( map<string, multiset<double> >::iterator var = varVals.begin(); var != varVals.end(); ++var )
            {
                double varInConsVal = (**cond).valuate( var->first, _allVariables.size(), true, _preferEquation );
                if( varInConsVal != 0 )
                    varVals.at( var->first ).insert( varInConsVal );
            }
        }
        #ifdef VS_DEBUG_VARIABLE_VALUATIONS
        for( map<string, multiset<double> >::const_iterator var = varVals.begin(); var != varVals.end(); ++var )
        {
            cout << var->first << ":  ";
            for( multiset<double>::const_iterator varVal = var->second.begin(); varVal != var->second.end(); ++varVal )
                cout <<  setprecision(10) << *varVal << " | ";
            cout << endl;
        }
        #endif
        // Find the variable which has in a constraint the best valuation. If more than one have the highest valuation, 
        // then choose the one having the higher valuation according to the method argument "_allVariables".
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
                        bestVar = var;
                }
                else if( var->second.size() == 1 )
                    bestVar = var;
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
                            break;
                        ++varInConsVal;
                        ++bestVarInConsVal;
                    }
                    if( varInConsVal == var->second.end() && bestVarInConsVal != bestVar->second.end() )
                        bestVar = var;
                }
            }
            else if( !var->second.empty() && bestVar->second.empty() )
                bestVar = var;
            ++var;
        }
        if( index() == "0" || (isRoot() && index() == "") )
        {
            setIndex( (*bestVar).first );
            return true;
        }
        else
        {
            if( index().compare( (*bestVar).first ) != 0 )
            {
                setIndex( (*bestVar).first );
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
    void State::addCondition( const smtrat::Constraint* _constraint, const ConditionSet& _originalConditions, const unsigned _valutation, const bool _recentlyAdded )
    {
        // Check if the constraint is variable-free and consistent. If so, discard it.
        unsigned constraintConsistency = _constraint->isConsistent();
        assert( constraintConsistency != 0 );
        if( constraintConsistency != 1 )
        {
            // Check if the condition already exists.
            mConditionsSimplified = false;
            mToHighDegree         = false;
            mMarkedAsDeleted      = false;
            // The state is not a leaf.
            if( index() != "" && index() != "0" )
            {
                if( _recentlyAdded )
                    mHasRecentlyAddedConditions = true;
                bool constraintWithFinitlyManySolutionCandidatesInIndexExists = false;
                for( StateVector::const_iterator child = children().begin(); child != children().end(); ++child )
                {
                    if( (**child).pOriginalCondition() != NULL )
                        constraintWithFinitlyManySolutionCandidatesInIndexExists = true;
                    break;
                }
                // Does the constraint contain the variable to eliminate.
                if( _constraint->variables().find( index() ) == _constraint->variables().end()
                        || constraintWithFinitlyManySolutionCandidatesInIndexExists )
                {
                    rConditions().push_back( new Condition( _constraint, _valutation, true, _originalConditions, _recentlyAdded ) );
                    if( mpVariableBounds != NULL && mpVariableBounds->addBound( _constraint, rConditions().back() ) )
                        mTestCandidateCheckedForBounds = false;
                }
                else
                {
                    rConditions().push_back( new Condition( _constraint, _valutation, false, _originalConditions, _recentlyAdded ) );
                    if( mpVariableBounds != NULL && mpVariableBounds->addBound( _constraint, rConditions().back() ) )
                        mTestCandidateCheckedForBounds = false;
                }
            }
            // The state is a leaf.
            else
            {
                rConditions().push_back( new Condition( _constraint, _valutation, false, _originalConditions, false ) );
                if( mpVariableBounds != NULL && mpVariableBounds->addBound( _constraint, rConditions().back() ) )
                    mTestCandidateCheckedForBounds = false;
            }
        }
    }
    
    /**
     * Checks whether no condition* in this state does point to a deleted condition.
     * This is just for debug purpose.
     * 
     * @return True, if all conditions are valid.
     */
    bool State::checkConditions() 
    {
        for( ConditionList::const_iterator cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            if( *cond == NULL )
                return false;
            for( ConditionSet::const_iterator oCond = (*cond)->originalConditions().begin(); oCond != (*cond)->originalConditions().end(); ++oCond )
                if( *oCond == NULL ) 
                    return false;
        }
        for( ConflictSets::const_iterator conflictSet = conflictSets().begin(); conflictSet != conflictSets().end(); ++conflictSet )
        {
            for( ConditionSetSetSet::const_iterator condSetSet = conflictSet->second.begin(); condSetSet != conflictSet->second.end(); ++condSetSet )
            {
                for( ConditionSetSet::const_iterator condSet = condSetSet->begin(); condSet != condSetSet->end(); ++condSet )
                {
                    for( ConditionSet::const_iterator cond = condSet->begin(); cond != condSet->end(); ++cond )
                    {
                        if( *cond == NULL ) 
                            return false;
                        if( (*cond)->pOriginalConditions() == NULL ) 
                            return false;
                        for( ConditionSet::const_iterator oCond = (*cond)->originalConditions().begin(); oCond != (*cond)->originalConditions().end(); ++oCond )
                            if( *oCond == NULL )
                                return false;
                    }
                }
            }
        }
        if( hasSubstitutionResults() )
        {
            for( SubstitutionResults::iterator subResult = rSubstitutionResults().begin(); subResult != substitutionResults().end(); ++subResult )
            {
                for( SubstitutionResult::iterator condConj = subResult->begin(); condConj != subResult->end(); ++condConj )
                {
                    for( ConditionList::iterator cond = condConj->first.begin(); cond != condConj->first.end(); ++cond )
                    {
                        if( *cond == NULL )
                            return false;
                        for( ConditionSet::iterator oCond = (**cond).pOriginalConditions()->begin(); oCond != (**cond).originalConditions().end(); ++oCond )
                            if( *oCond == NULL )
                                return false;
                    }
                }
            }
        }
        return true;
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
    int State::deleteOrigins( set<const Condition*>& _originsToDelete )
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
                        rSubstitution().rOriginalConditions().erase( oCondInSub++ );
                    else
                        ++oCondInSub;
                }
                if( substitution().originalConditions().empty() )
                {
                    // If the substitutions original conditions are all deleted, then delete the corresponding child.
                    // TODO: Maybe it is better to keep these children/test candidates.
                    int result = 0;
                    if( pOriginalCondition() != NULL ) result = -1;
                    return result;
                }
            }
        }
        // Remove conditions from the currently considered condition vector, which are originated by any of the given origins.
        bool conditionDeleted = false;
        bool recentlyAddedConditionLeft = false;
        set<const Condition*> deletedConditions = set<const Condition*>();
        set<const Condition*> originsToRemove = set<const Condition*>();
        for( auto originToDelete = _originsToDelete.begin(); originToDelete != _originsToDelete.end(); ++originToDelete )
        {
            auto condition = rConditions().begin();
            while( condition != conditions().end() )
            {
                if( (*condition)->originalConditions().find( *originToDelete ) != (*condition)->originalConditions().end() )
                {
                    if( mpVariableBounds != NULL )
                    {
                        const ex var = mpVariableBounds->removeBound( (*condition)->pConstraint(), *condition );
                        if( is_exactly_a<symbol>( var ) )
                        {
                            for( auto condB = rConditions().begin(); condB != conditions().end(); ++condB )
                            {
                                if( (*condB)->constraint().variables().find( ex_to<symbol>( var ).get_name() ) != (*condB)->constraint().variables().end() )
                                {
                                    originsToRemove.insert( *condB );
                                    (*condB)->rRecentlyAdded() = true;
                                    (*condB)->rFlag() = (*condB)->constraint().hasVariable( index() );
                                }
                            }
                        }
                    }
                    // Delete the condition to delete from the set of conditions with too high degree to
                    // be entirely used for test candidate generation.
                    mpTooHighDegreeConditions->erase( *condition );
                    deletedConditions.insert( *condition );
                    originsToRemove.insert( *condition );
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
                mType              = COMBINE_SUBRESULTS;
            }
            mInconsistent = false;
            mHasRecentlyAddedConditions = recentlyAddedConditionLeft;
        }
        mToHighDegree      = false;
        mMarkedAsDeleted   = false;
        mTryToRefreshIndex = true;
        // Delete everything originated by it in all children of this state.
        deleteOriginsFromChildren( originsToRemove );
        // Delete the conditions in the conflict sets which are originated by any of the given origins.
        deleteOriginsFromConflictSets( _originsToDelete, false );     
        // Delete the conditions.
        while( !deletedConditions.empty() )
        {
            const Condition* pCond = *deletedConditions.begin();
            deletedConditions.erase( deletedConditions.begin() );
            delete pCond;
            pCond = NULL;
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
    void State::deleteConditions( set<const Condition*>& _conditionsToDelete )
    {
        if( _conditionsToDelete.empty() ) return;    
        // Delete the conditions to delete from the set of conditions with too high degree to
        // be entirely used for test candidate generation.
        for( auto cond = _conditionsToDelete.begin(); cond != _conditionsToDelete.end(); ++cond )
        {
            mpTooHighDegreeConditions->erase( *cond );
        }
        // Remove the given conditions from this state.
        bool conditionDeleted = false;
        bool recentlyAddedConditionLeft = false;
        set<const Condition*> originsToRemove = set<const Condition*>();
        for( auto cond = rConditions().begin(); cond != conditions().end(); )
        {
            // Delete the condition from the vector this state considers.
            if( _conditionsToDelete.find( *cond ) != _conditionsToDelete.end() )
            {
                if( mpVariableBounds != NULL )
                {
                    const ex var = mpVariableBounds->removeBound( (*cond)->pConstraint(), *cond );
                    if( is_exactly_a<symbol>( var ) )
                    {
                        for( auto condB = rConditions().begin(); condB != conditions().end(); ++condB )
                        {
                            if( (*condB)->constraint().variables().find( ex_to<symbol>( var ).get_name() ) != (*condB)->constraint().variables().end() )
                            {
                                originsToRemove.insert( *condB );
                                (*condB)->rRecentlyAdded() = true;
                                (*condB)->rFlag() = (*condB)->constraint().hasVariable( index() );
                            }
                        }
                    }
                }
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
                mType              = COMBINE_SUBRESULTS;
            }
            mInconsistent = false;
            mHasRecentlyAddedConditions = recentlyAddedConditionLeft;
        }
        originsToRemove.insert( _conditionsToDelete.begin(), _conditionsToDelete.end() );
        // Delete everything originated by the given conditions in all children of this state.
        deleteOriginsFromChildren( originsToRemove );
        // Delete the conditions from the conflict sets.
        deleteOriginsFromConflictSets( originsToRemove, true );
        // Delete everything originated by the conditions to delete in the state's children.
        deleteOriginsFromChildren( originsToRemove );
        mToHighDegree      = false;
        mMarkedAsDeleted   = false;
        mTryToRefreshIndex = true;
    }
    
    /**
     * Deletes everything originated by the given conditions in the children of this state.
     * 
     * @param _originsToDelete The condition for which to delete everything originated by them.
     */
    void State::deleteOriginsFromChildren( set<const Condition*>& _originsToDelete )
    {
        auto child = rChildren().begin();
        while( child != children().end() )
        {
            int result = (*child)->deleteOrigins( _originsToDelete );
            if( result < 0 )
                initConditionFlags();
            if( result < 1 )
            {
                ConflictSets::iterator conflictSet = rConflictSets().find( (*child)->pSubstitution() );
                if( conflictSet != conflictSets().end() )
                    rConflictSets().erase( conflictSet );
                State* toDelete = *child;
                child = rChildren().erase( child );
                delete toDelete;
            }
            else
                ++child;
        }
    }
    
    /**
     * Deletes everything originated by the given conditions in the conflict sets of this state.
     * 
     * @param _originsToDelete The condition for which to delete everything originated by them.
     */
    void State::deleteOriginsFromConflictSets( set<const Condition*>& _originsToDelete, bool _originsAreCurrentConditions )
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
                        if( _originsAreCurrentConditions )
                        {
                            if( _originsToDelete.find( *cond ) != _originsToDelete.end() )
                            {
                                condToDelOccured = true;
                                break;
                            }
                            else
                                updatedCondSet.insert( *cond );
                        }
                        else
                        {
                            ConditionSet::const_iterator condToDel = _originsToDelete.begin();
                            while( condToDel != _originsToDelete.end() )
                            {
                                if( (*cond)->originalConditions().find( *condToDel ) != (*cond)->originalConditions().end() )
                                    break;
                                ++condToDel;
                            }
                            if( condToDel == _originsToDelete.end() )
                                updatedCondSet.insert( *cond );
                            else
                            {
                                condToDelOccured = true;
                                break;
                            }
                        }
                        ++cond;
                    }
                    if( !condToDelOccured )
                        updatedCondSetSet.insert( updatedCondSet );
                    ++condSet;
                }
                if( !updatedCondSetSet.empty() )
                    updatedCondSetSetSet.insert( updatedCondSetSet );
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
                    rInconsistent() = false;
                if( mpVariableBounds != NULL && conflictSet->first != NULL && conflictSet->first->type() == ST_INVALID )
                {
                    for( auto oCond = conflictSet->first->originalConditions().begin(); oCond != conflictSet->first->originalConditions().end(); ++oCond )
                    {
                        (*oCond)->rFlag() = false;
                    }
                    const Substitution* subToDelete = conflictSet->first;
                    mpConflictSets->erase( conflictSet++ );
                    delete subToDelete;
                }
                else
                {
                    mpConflictSets->erase( conflictSet++ );
                }
            }
        }
        auto child = rChildren().begin();
        while( child != children().end() )
        {
            if( mpConflictSets->find( (*child)->pSubstitution() ) == mpConflictSets->end() )
            {
                // Delete the entry of the test candidate whose conflict set is empty
                // and set "inconsistent flag" of the corresponding child to false.
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
                if( (*child)->type() != SUBSTITUTION_TO_APPLY )
                {
                    (*child)->rType() = COMBINE_SUBRESULTS;
                    (*child)->rTakeSubResultCombAgain() = true;
                }
                (*child)->rInconsistent() = false;
            }
            ++child;
        }
    }
    
    /**
     * Deletes everything originated by the given conditions in the substitution results of this state.
     * 
     * @param _originsToDelete The conditions for which to delete everything originated by them.
     */
    void State::deleteOriginsFromSubstitutionResults( set<const Condition*>& _originsToDelete )
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
                    ConditionList conditionsToAdd = ConditionList();
                    ConditionList::iterator cond = condConj->first.begin();
                    while( cond != condConj->first.end() )
                    {
                        bool                   oCondsDeleted = false;
                        ConditionSet::iterator oCond         = (**cond).pOriginalConditions()->begin();
                        while( oCond != (**cond).originalConditions().end() )
                        {
                            if( _originsToDelete.find( *oCond ) != _originsToDelete.end() )
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
                                conditionsToAdd.push_back( new Condition( (**oCond).pConstraint(), (**cond).valuation(), false, oConds ) );
                                ++oCond;
                            }
                            const Condition* rpCond = *cond;
                            cond             = condConj->first.erase( cond );
                            condConj->second = false;
                            delete rpCond;
                            rpCond = NULL;
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
                                // If the currently considered condition conjunction in the currently considered substitution result
                                // is part of the substitution result combination of this state.
                                if( subResComb->second == subResultConjunctionIndex )
                                {
                                    // Remove this entry of the substitution result combinations.
                                    rSubResultCombination().erase( subResComb );
                                }
                                // If the currently considered condition conjunction in the currently considered substitution result
                                // is NOT part of the substitution result combination of this state, but another condition conjunction in
                                // the currently considered substitution result with higher index, decrease this index.
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
     * Adds a state as child to this state with the given substitution.
     *
     * @param _substitution The substitution to generate the state for.
     * 
     * @return True, if a state has been added as child to this state.
     */
    bool State::addChild( const Substitution& _substitution )
    {
        if( !updateOCondsOfSubstitutions( _substitution ) )
        {
            State* state = new State( this, _substitution, mpVariableBounds != NULL );
            const smtrat::ConstraintSet& sideConds = _substitution.sideCondition();
            for( auto sideCond = sideConds.begin(); sideCond != sideConds.end(); ++sideCond )
            {
                std::vector<DisjunctionOfConditionConjunctions> subResults = std::vector<DisjunctionOfConditionConjunctions>();
                subResults.push_back( DisjunctionOfConditionConjunctions() );
                subResults.back().push_back( ConditionList() );
                subResults.back().back().push_back( new Condition( *sideCond, state->treeDepth(), false, _substitution.originalConditions(), false ) );
                state->addSubstitutionResults( subResults );
                state->rType() = SUBSTITUTION_TO_APPLY;
            }
            state->updateValuation();
            rChildren().push_back( state );
            return true;
        }
        else return false;
    }

    /**
     *  Updates the valuation of this state.
     */
    void State::updateValuation()
    {
        if( toHighDegree() )
        {
            mValuation = 1;
            updateBackendCallValuation();
        }
        else
        {
            // The substitution's valuation is a number between 1 and 9 and the tree depth is equal to
            // number of variables plus one. 4.294.967.295
            if( !isRoot() ) mValuation = 100 * treeDepth() + 10 * substitution().valuate();
            else mValuation = 1;
            if( isInconsistent() ) mValuation += 7;
            else if( hasRecentlyAddedConditions() ) mValuation += 6;
            else if( type() == TEST_CANDIDATE_TO_GENERATE && conditions().empty() ) mValuation += 5;
            else
            {
                if( type() == SUBSTITUTION_TO_APPLY ) mValuation += 2;
                else if( type() == TEST_CANDIDATE_TO_GENERATE ) mValuation += 4;
                else mValuation += 3;
            }
        }
    }

    /**
     * Valuates the state's currently considered conditions according to a backend call.
     * 
     * Note: The settings are currently optimized for CAD backend calls.
     */
    void State::updateBackendCallValuation()
    {
        symtab occuringVars = symtab();
        set< smtrat::Constraint_Relation > relationSymbols = set< smtrat::Constraint_Relation >();
        for( auto cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            const symtab& vars = (*cond)->constraint().variables();
            occuringVars.insert( vars.begin(), vars.end() );
            relationSymbols.insert( (*cond)->constraint().relation() );
        }
        mBackendCallValuation = 300000*occuringVars.size();
        if( relationSymbols.find( smtrat::CR_EQ ) != relationSymbols.end() )
        {
            mBackendCallValuation += 200000;
        }
        else if( relationSymbols.find( smtrat::CR_LEQ ) != relationSymbols.end() || relationSymbols.find( smtrat::CR_GEQ ) != relationSymbols.end() )
        {
            mBackendCallValuation += 100000;
        }
        mBackendCallValuation += conditions().size();
    }
    
    /**
     * Passes the original conditions of the covering set of the conflicts of this state to its father.
     */
    void State::passConflictToFather( bool _checkConflictForSideCondition, bool _includeInconsistentTestCandidates )
    {
        assert( isInconsistent() );
        // Determine a covering set of the conflict sets.
        ConditionSet covSet         = ConditionSet();
        ConditionSetSetSet confSets = ConditionSetSetSet();
        ConflictSets::iterator nullConfSet = rConflictSets().find( NULL );
        if( nullConfSet != conflictSets().end() && !_includeInconsistentTestCandidates )
            confSets.insert( nullConfSet->second.begin(), nullConfSet->second.end() );
        else
        {
            for( ConflictSets::iterator confSet = rConflictSets().begin(); confSet != conflictSets().end(); ++confSet )
                confSets.insert( confSet->second.begin(), confSet->second.end() );
        }
        coveringSet( confSets, covSet, treeDepth() );
        #ifdef VS_LOG_INFSUBSETS
        set< const smtrat::Constraint* > constraints = set< const smtrat::Constraint* >();
        for( ConditionSet::const_iterator cond = covSet.begin(); cond != covSet.end(); ++cond )
        {
            constraints.insert( (**cond).pConstraint() );
        }
        smtrat::Module::addAssumptionToCheck( constraints, false, "VSModule_IS_1" );
        #endif
        // Get the original conditions to the covering set.
        ConditionSet coverSetOConds = ConditionSet();
        bool coverSetOCondsContainIndexOfFather = false;
        bool sideConditionIsPartOfConflict = !_checkConflictForSideCondition || (pOriginalCondition() == NULL || originalCondition().constraint().relation() != smtrat::CR_EQ);
        const smtrat::ConstraintSet& subsSideConds = substitution().sideCondition();
        for( ConditionSet::iterator cond = covSet.begin(); cond != covSet.end(); ++cond )
        {
            // Add the original conditions of the condition to the conflict set.
            if( !(**cond).originalConditions().empty() )
            {
                ConditionSet::iterator oCond = (**cond).originalConditions().begin();
                while( oCond != (**cond).originalConditions().end() )
                {
                    if( (**oCond).constraint().hasVariable( father().index() ) )
                        coverSetOCondsContainIndexOfFather = true;
                    coverSetOConds.insert( *oCond );
                    oCond++;
                }
            }
            sideConditionIsPartOfConflict |= subsSideConds.find( (*cond)->pConstraint() ) != subsSideConds.end();
        }
        if( !sideConditionIsPartOfConflict )
        {
            for( auto cond = rFather().rConditions().begin(); cond != father().conditions().end(); ++cond )
                (*cond)->rFlag() = true;
        }
        // If a test candidate was provided by an equation and its side condition hold always,
        // add the corresponding constraint to the conflict set. (Because we omit the other test candidates )
        if( pOriginalCondition() != NULL )
        {
            // Add the corresponding original condition to the conflict set.
            coverSetOConds.insert( pOriginalCondition() );
            // This original condition of course contains the index of the father, as it served as test candidate provider.
            coverSetOCondsContainIndexOfFather = true;
        }
        ConditionSetSet conflictSet = ConditionSetSet();
        conflictSet.insert( coverSetOConds );
        assert( !coverSetOConds.empty() );
        // Add the original conditions of the covering set as a conflict set to the father.
        if( !coverSetOCondsContainIndexOfFather )
            rFather().addConflictSet( NULL, conflictSet );
        else
            rFather().addConflictSet( pSubstitution(), conflictSet );
        // Delete all children, the conflict sets and the conditions of this state.
        mpConflictSets->clear();
        while( !children().empty() )
        {
            State* toDelete = rChildren().back();
            rChildren().pop_back();
            delete toDelete;
        }
        mpTooHighDegreeConditions->clear();
        while( !conditions().empty() )
        {
            const Condition* pCond = rConditions().back();
            rConditions().pop_back();
            if( mpVariableBounds != NULL )
                mpVariableBounds->removeBound( pCond->pConstraint(), pCond );
            delete pCond;
            pCond = NULL;
        }
        // Reset all necessary flags.
        rHasRecentlyAddedConditions() = false;
        rTakeSubResultCombAgain()     = false;
        rFather().rMarkedAsDeleted() = false;
        bool fixedConditions = false;
        if( hasSubResultsCombination() )
        {
            if( subResultCombination().size() == 1 )
                fixedConditions = substitutionResults().at( subResultCombination().back().first ).size() == 1;
        }
        else
            fixedConditions = true;
        if( coverSetOCondsContainIndexOfFather && !fixedConditions )
        {
            rMarkedAsDeleted() = false;
            rInconsistent() = false;
            rType()    = COMBINE_SUBRESULTS;
        }
    }
    
    /**
     * Checks whether the currently considered conditions, which have been considered for test candidate 
     * construction, form already a conflict.
     * 
     * @return True, if they form a conflict.
     */
    bool State::hasLocalConflict()
    {
        if( conflictSets().empty() || !tooHighDegreeConditions().empty() || !hasOnlyInconsistentChildren() ) return false;
        #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
        printAlone();
        #endif
        // Construct the local conflict consisting of all of the currently considered conditions,
        // which have been considered for test candidate construction.
        ConditionSet localConflictSet = ConditionSet();
        for( auto cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            if( (*cond)->flag() ) localConflictSet.insert( *cond );
        }
        // Check whether the local conflict set covers for each test candidate, its conditions have generated,
        // one of its conflict sets.
        #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
        cout << "local conflict:   { ";
        for( auto iter = localConflictSet.begin(); iter != localConflictSet.end(); ++iter )
            cout << (*iter)->constraint() << " ";
        cout << "}" << endl;
        #endif
        ConditionSet infSubset = ConditionSet();
        bool containsConflictToCover = false;
        for( auto conflict = conflictSets().begin(); conflict != conflictSets().end(); ++conflict )
        {
            containsConflictToCover = true;
            for( auto condSetSet = conflict->second.begin(); condSetSet != conflict->second.end(); ++condSetSet )
            {
                auto condSet = condSetSet->begin();
                for( ; condSet != condSetSet->end(); ++condSet )
                {
                    auto condA = condSet->begin();
                    auto condB = localConflictSet.begin();
                    assert( condA != condSet->end() );
                    #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
                    cout << "covers:   { ";
                    for( auto iter = condSet->begin(); iter != condSet->end(); ++iter )
                        cout << (*iter)->constraint() << " ";
                    cout << "}  ??";
                    #endif
                    while( condA != condSet->end() &&  condB != localConflictSet.end() )
                    {
                        if( Condition::condComp()( *condB, *condA ) )
                            ++condB;
                        else if( Condition::condComp()( *condA, *condB ) )
                            break;
                        else
                        {
                            ++condA;
                            ++condB;
                        }
                    }
                    if( condA == condSet->end() )
                    {
                        infSubset.insert( condSet->begin(), condSet->end() );
                        #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
                        cout << "   Yes!" << endl;
                        #endif
                        break;
                    }
                    else
                    {
                        #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
                        cout << "   No!" << endl;
                        #endif
                    }
                }
                if( condSet == condSetSet->end() )
                {
                    #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
                    cout << "No conflict set in conflict is covered!" << endl;
                    #endif
                    return false;
                }
                #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
                else
                {
                    cout << "A conflict set in conflict is covered!" << endl;
                }
                #endif
            }
        }
        if( containsConflictToCover )
        {
            ConditionSetSet localConflict = ConditionSetSet();
            localConflict.insert( infSubset );
            addConflictSet( NULL, localConflict );
            return true;
        }
        else
            return false;
    }

    /**
     * Checks whether the test candidate of this state is valid against the variable intervals
     * in the father of this state.
     * 
     * @return True, if the test candidate of this state is valid against the variable intervals;
     *          False, otherwise.
     */
    bool State::checkTestCandidatesForBounds()
    {
        if( mTestCandidateCheckedForBounds ) return true;
        mTestCandidateCheckedForBounds = true;
        if( !isRoot() )
        {
            if( substitution().type() == ST_MINUS_INFINITY ) return true;
            #ifdef VS_DEBUG_VARIABLE_BOUNDS
            cout << ">>> Check test candidate  " << substitution() << "  against:" << endl;
            father().variableBounds().print( cout, ">>>    " );
            #endif
            ConditionSet conflict = ConditionSet();
            vector< DoubleInterval > solutionSpaces = solutionSpace( conflict );
            if( solutionSpaces.empty() )
            {
                ConditionSetSet conflicts = ConditionSetSet();
                conflicts.insert( conflict );
                pFather()->addConflictSet( pSubstitution(), conflicts );
                return false;
            }
        }
        return true;
    }
    
    /**
     * Determines the solution space of the test candidate of this state regarding to
     * the variable bounds of the father. The solution space consists of one or two
     * disjoint intervals.
     * 
     * @param _conflictReason If the solution space is empty, the conditions being
     *                         responsible for this conflict are stored in here.
     * @return The disjoint intervals representing the solution space.
     */
    vector< DoubleInterval > State::solutionSpace( ConditionSet& _conflictReason )
    {
        vector< DoubleInterval > result = vector< DoubleInterval >();
        assert( !isRoot() );
        if( substitution().type() == ST_MINUS_INFINITY )
        {
            if( rFather().rVariableBounds().getDoubleInterval( substitution().varAsEx() ).leftType() == DoubleInterval::INFINITY_BOUND )
            {
                result.push_back( DoubleInterval::unboundedInterval() );
            }
            else
            {
                set< const Condition* > conflictBounds = father().variableBounds().getOriginsOfBounds( ex_to<symbol>( substitution().varAsEx() ) );
                _conflictReason.insert( conflictBounds.begin(), conflictBounds.end() );
            }
            return result;
        }
        else
        {
            evaldoubleintervalmap intervals = rFather().rVariableBounds().getIntervalMap();
            DoubleInterval solutionSpaceConst = DoubleInterval::evaluate( substitution().term().constantPart(), intervals );
            DoubleInterval solutionSpaceFactor = DoubleInterval::evaluate( substitution().term().factor(), intervals );
            DoubleInterval solutionSpaceRadicand = DoubleInterval::evaluate( substitution().term().radicand(), intervals );
            DoubleInterval solutionSpaceSqrt = solutionSpaceRadicand.sqrt();
            DoubleInterval solutionSpaceDenom = DoubleInterval::evaluate( substitution().term().denominator(), intervals );
            DoubleInterval solutionSpace = solutionSpaceFactor * solutionSpaceSqrt;
            solutionSpace = solutionSpace + solutionSpaceConst;
            #ifdef VS_DEBUG_VARIABLE_BOUNDS
            cout << ">>> Results in:" << endl;
            cout << ">>>    constant part      : " << solutionSpaceConst << endl;
            cout << ">>>    factor part        : " << solutionSpaceFactor << endl;
            cout << ">>>    radicand part      : " << solutionSpaceRadicand << endl;
            cout << ">>>    square root part   : " << solutionSpaceSqrt << endl;
            cout << ">>>    denominator part   : " << solutionSpaceDenom << endl;
            cout << ">>>    numerator part     : " << solutionSpace << endl;
            #endif
            DoubleInterval resA;
            DoubleInterval resB;
            bool splitOccurred = solutionSpace.div_ext( resA, resB, solutionSpaceDenom );
            symbol subVar = ex_to<symbol>( substitution().varAsEx() );
            const DoubleInterval& subVarInterval = intervals[subVar];
            if( substitution().type() == ST_PLUS_EPSILON && resA.leftType() != DoubleInterval::INFINITY_BOUND )
            {
                if( resA.rightType() == DoubleInterval::INFINITY_BOUND || resA.right() == DBL_MAX )
                {
                    resA = DoubleInterval( resA.left(), DoubleInterval::STRICT_BOUND, 0, DoubleInterval::INFINITY_BOUND );
                    if( splitOccurred )
                    {
                        resB = DoubleInterval( resB.left(), DoubleInterval::STRICT_BOUND, 0, DoubleInterval::INFINITY_BOUND );
                    }
                }
                else
                {
                    resA = DoubleInterval( resA.left(), DoubleInterval::STRICT_BOUND, std::nextafter( resA.right(), INFINITY ), DoubleInterval::WEAK_BOUND );
                    if( splitOccurred )
                    {
                        resB = DoubleInterval( resB.left(), DoubleInterval::STRICT_BOUND, std::nextafter( resB.right(), INFINITY ), DoubleInterval::WEAK_BOUND );
                    }
                }
            }
            #ifdef VS_DEBUG_VARIABLE_BOUNDS
            cout << ">>>    division part 1    : " << resA << endl;
            #endif
            resA = resA.intersect( subVarInterval );
            #ifdef VS_DEBUG_VARIABLE_BOUNDS
            cout << ">>>    intersection part 1: " << resA << endl;
            #endif
            if( !resA.empty() )
            {
                result.push_back( resA );
            }
            if( splitOccurred )
            {
                #ifdef VS_DEBUG_VARIABLE_BOUNDS
                cout << ">>>    division part 2: " << resB << endl;
                #endif
                resB = resB.intersect( subVarInterval );
                #ifdef VS_DEBUG_VARIABLE_BOUNDS
                cout << ">>>    intersection part 1: " << resB << endl;
                #endif
                if( !resB.empty() )
                {
                    result.push_back( resB );
                }
            }
            if( result.empty() )
            {
                symtab vars = substitution().termVariables();
                vars[substitution().variable()] = substitution().varAsEx();
                set< const Condition* > conflictBounds = father().variableBounds().getOriginsOfBounds( vars );
                _conflictReason.insert( conflictBounds.begin(), conflictBounds.end() );
                _conflictReason.insert( substitution().originalConditions().begin(), substitution().originalConditions().end() );
            }
        }
        return result;
    }

     /**
     * Checks whether there are no zeros for the left-hand side of the constraint of the given condition.
     * 
     * @param _condition The condition to check.
     * @return True, if the constraint of the left-hand side of the given condition has no roots 
     *          in the variable bounds of this state.
     */
    bool State::hasRootsInVariableBounds( const Condition* _condition, bool _useSturmSequence )
    {
        #ifdef VS_DEBUG_ROOTS_CHECK
        cout << __func__ << ":  " << _condition->constraint() << endl;
        #endif
        symbol sym;
        const smtrat::Constraint& cons = _condition->constraint();
        cons.variable( index(), sym );
        evaldoubleintervalmap intervals = evaldoubleintervalmap();
        if( cons.variables().size() > 1 )
            intervals = rVariableBounds().getIntervalMap();
        else
        {
            DoubleInterval varDomain = rVariableBounds().getDoubleInterval( sym );
            pair<numeric, numeric> cb = cons.cauchyBounds();
            #ifdef VS_DEBUG_ROOTS_CHECK
            cout << "Cauchy bounds of  " << cons.lhs() << "  are  " << cb.first << " and " << cb.second << endl;
            #endif
            DoubleInterval cbInterval = DoubleInterval( -cb.second, DoubleInterval::STRICT_BOUND, cb.second, DoubleInterval::STRICT_BOUND );
            varDomain = varDomain.intersect( cbInterval );
            #ifdef VS_DEBUG_ROOTS_CHECK
            cout << varDomain << endl;
            #endif
            intervals[sym] = varDomain;
        }
        DoubleInterval solutionSpace = DoubleInterval::evaluate( cons.lhs(), intervals );
        smtrat::Constraint_Relation rel = cons.relation();
        // TODO: if the condition is an equation and the degree in the index less than 3, 
        // then it is maybe better to consider the according test candidates
        if( rel == smtrat::CR_GREATER || rel == smtrat::CR_LESS || rel == smtrat::CR_NEQ )
        {
            if( solutionSpace.leftType() == DoubleInterval::STRICT_BOUND && solutionSpace.left() == 0 )
            {
                solutionSpace.setLeftType( DoubleInterval::WEAK_BOUND );
            }
        }
        #ifdef VS_DEBUG_ROOTS_CHECK
        cout << "solutionSpace: " << solutionSpace << endl;
        #endif
        if( solutionSpace.contains( 0 ) )
        {
            if( _useSturmSequence && cons.variables().size() == 1 )
            {
                RationalUnivariatePolynomial rup = RationalUnivariatePolynomial( cons.lhs(), sym );
                list<RationalUnivariatePolynomial> seq = RationalUnivariatePolynomial::standardSturmSequence( rup, rup.diff() );
                numeric leftBound = rationalize( numeric( intervals.begin()->second.left() ) );
                numeric rightBound = rationalize( numeric( intervals.begin()->second.right() ) );
                unsigned numberOfRoots = RationalUnivariatePolynomial::signVariations( seq, leftBound ) - RationalUnivariatePolynomial::signVariations( seq, rightBound );
                exmap assignment = exmap();
                assignment[sym] = leftBound;
                ex imageOfLeftBound = cons.lhs().subs( assignment );
                assert( is_exactly_a<numeric>( imageOfLeftBound ) );
                assignment[sym] = rightBound;
                ex imageOfRightBound = cons.lhs().subs( assignment );
                assert( is_exactly_a<numeric>( imageOfRightBound ) );
                if( imageOfLeftBound == 0 )
                {
                    ++numberOfRoots;
                }
                if( imageOfRightBound == 0 )
                {
                    if( intervals.begin()->second.rightType() == DoubleInterval::STRICT_BOUND && numberOfRoots != 0 )
                        --numberOfRoots;
                    if( intervals.begin()->second.rightType() == DoubleInterval::WEAK_BOUND )
                        ++numberOfRoots;
                }
                #ifdef VS_DEBUG_ROOTS_CHECK
                cout << "Image of left bound                     : " << imageOfLeftBound << endl;
                cout << "Image of right bound                    : " << imageOfRightBound << endl;
                cout << "Number of roots according sturm sequence: " << numberOfRoots << endl;
                #endif
                bool constraintInconsistent = false;
                if( numberOfRoots == 0 )
                {
                    if( cons.relation() == smtrat::CR_EQ )
                        constraintInconsistent = true;
                    else if( imageOfLeftBound > 0 && (cons.relation() == smtrat::CR_LESS || cons.relation() == smtrat::CR_LEQ) )
                        constraintInconsistent = true;
                    else if( imageOfLeftBound < 0 && (cons.relation() == smtrat::CR_GREATER || cons.relation() == smtrat::CR_GEQ) )
                        constraintInconsistent = true;
                }
                else if( numberOfRoots == 1 )
                {
                    if( imageOfLeftBound > 0 && imageOfRightBound > 0 && cons.relation() == smtrat::CR_LESS )
                        constraintInconsistent = true;
                    if( imageOfLeftBound < 0 && imageOfRightBound < 0 && cons.relation() == smtrat::CR_GREATER )
                        constraintInconsistent = true;
                }
                if( constraintInconsistent )
                {
                    ConditionSet origins = ConditionSet();
                    origins.insert( _condition );
                    set< const Condition* > conflictingBounds = variableBounds().getOriginsOfBounds( sym );
                    origins.insert( conflictingBounds.begin(), conflictingBounds.end() );
                    ConditionSetSet conflicts = ConditionSetSet();
                    conflicts.insert( origins );
                    addConflictSet( NULL, conflicts );
                    rInconsistent() = true;
                    #ifdef VS_DEBUG_ROOTS_CHECK
                    cout << "  -> false (1)" << endl;
                    #endif
                    return false;
                }
                if( numberOfRoots > 0 )
                {
                #ifdef VS_DEBUG_ROOTS_CHECK
                cout << "  -> true (1)" << endl;
                #endif
                return true;
                }
            }
            else
            {
                #ifdef VS_DEBUG_ROOTS_CHECK
                cout << "  -> true (3)" << endl;
                #endif
                return true;
            }
        }
        bool constraintInconsistent = false;
        if( cons.relation() == smtrat::CR_EQ )
            constraintInconsistent = true;
        else if( solutionSpace.left() > 0 && cons.relation() == smtrat::CR_LEQ )
            constraintInconsistent = true;
        else if( solutionSpace.right() < 0 && cons.relation() == smtrat::CR_GEQ )
            constraintInconsistent = true;
        else if( solutionSpace.left() >= 0 && cons.relation() == smtrat::CR_LESS )
            constraintInconsistent = true;
        else if( solutionSpace.right() <= 0 && cons.relation() == smtrat::CR_GREATER )
            constraintInconsistent = true;
        ConditionSet origins = ConditionSet();
        origins.insert( _condition );
        symtab vars = cons.variables();
        set< const Condition* > conflictingBounds = variableBounds().getOriginsOfBounds( vars );
        origins.insert( conflictingBounds.begin(), conflictingBounds.end() );
        ConditionSetSet conflicts = ConditionSetSet();
        conflicts.insert( origins );
        Substitution* sub = NULL;
        if( !constraintInconsistent )
        {
            smtrat::ConstraintSet constraints = smtrat::ConstraintSet();
            constraints.insert( _condition->pConstraint() );
            ConditionSet subsOrigins = ConditionSet();
            subsOrigins.insert( _condition );
            sub = new Substitution( index(), ex( sym ), ST_INVALID, subsOrigins, constraints );
        }
        addConflictSet( sub, conflicts );
        #ifdef VS_DEBUG_ROOTS_CHECK
        cout << "  -> false (2)" << endl;
        #endif
        return false;
    }

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
            for( StateVector::const_iterator child = children().begin(); child != children().end(); ++child )
                (**child).print( _initiation + "      ", _out );
        else _out << _initiation << "      no" << endl;
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
        switch( type() )
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
            _out << _initiation << "               hasRecentlyAddedConditions: yes" << endl;
        else 
            _out << _initiation << "               hasRecentlyAddedConditions: no" << endl;
        if( isInconsistent() ) 
            _out << _initiation << "                           isInconsistent: yes" << endl;
        else
            _out << _initiation << "                           isInconsistent: no" << endl;
        if( conditionsSimplified() )
            _out << _initiation << "                     conditionsSimplified: yes" << endl;
        else
            _out << _initiation << "                     conditionsSimplified: no" << endl;
        if( subResultsSimplified() )
            _out << _initiation << "                     subResultsSimplified: yes" << endl;
        else
            _out << _initiation << "                     subResultsSimplified: no" << endl;
        if( takeSubResultCombAgain() )
            _out << _initiation << "                   takeSubResultCombAgain: yes" << endl;
        else
            _out << _initiation << "                   takeSubResultCombAgain: no" << endl;
        if( toHighDegree() )
            _out << _initiation << "                             toHighDegree: yes" << endl;
        else
            _out << _initiation << "                             toHighDegree: no" << endl;
        if( markedAsDeleted() )
            _out << _initiation << "                          markedAsDeleted: yes" << endl;
        else
            _out << _initiation << "                          markedAsDeleted: no" << endl;
        if( pOriginalCondition() != NULL )
        {
            _out << _initiation << "                       original condition: ";
            _out << originalCondition().constraint().toString() << " [";
            _out << pOriginalCondition() << "]" << endl;
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
        if( mpVariableBounds != NULL )
        {
            _out << _initiation << endl;
            mpVariableBounds->print( _out, _initiation );
            _out << _initiation << endl;
        }
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
        for( ConditionList::const_iterator cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            _out << _initiation << "   ";
            if( _onlyAsConstraints ) (**cond).constraint().print();
            else (**cond).print( _out );
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

                    for( ConditionList::const_iterator cond = condConjunction->first.begin(); cond != condConjunction->first.end(); ++cond )
                    {
                        if( cond != condConjunction->first.begin() ) _out << " and ";
                        (**cond).print( _out );
                    }
                    _out << " )";
                    if( condConjunction->second ) _out << "_[True]  ";
                    else _out << "_[False]  ";
                    SubstitutionResult::const_iterator nextCondConjunction = condConjunction;
                    ++nextCondConjunction;
                    if( nextCondConjunction != subResult->end() ) _out << endl;
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
            if( hasSubResultsCombination() )
            {
                _out << _initiation << "Substitution result combination:" << endl;
                for( SubResultCombination::const_iterator subResComb = mpSubResultCombination->begin(); subResComb != mpSubResultCombination->end();
                        ++subResComb )
                {
                    _out << _initiation << "   (  ";
                    for( ConditionList::const_iterator cond = mpSubstitutionResults->at( subResComb->first ).at( subResComb->second ).first.begin();
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
        // Greatest tree depth of the original conditions of the conditions in the covering set.
        unsigned greatestTreeDepth = 0;
        for( ConditionSetSetSet::const_iterator conflictSet = _conflictSets.begin(); conflictSet != _conflictSets.end(); ++conflictSet )
        {
            if( !conflictSet->empty() )
            {
                // Greatest tree depth of the original conditions of the conditions in the
                // currently best set of conditions in this conflict set.
                unsigned greatestTreeDepthConflictSet = 0;
                // The number of conditions in the currently best set of conditions, which are
                // not covered of the so far created covering set.
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
                        assert( *condition != NULL );
                        for( ConditionSet::const_iterator oCond = (**condition).originalConditions().begin();
                                oCond != (**condition).originalConditions().end(); ++oCond )
                        {
                            assert( *oCond != NULL );
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

