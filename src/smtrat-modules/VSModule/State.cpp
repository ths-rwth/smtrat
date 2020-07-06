/**
 * Class to create a state object.
 * @author Florian Corzilius
 * @since 2010-05-11
 * @version 2013-10-24
 */

#include "State.h"
//#include <smtrat-modules/Module.h>
#include <carl/interval/set_theory.h>
#include <carl/core/polynomialfunctions/SturmSequence.h>
#include <cmath>
#include <float.h>
#include <numeric>
#include <carl/core/polynomialfunctions/RootBounds.h>
#include <carl/core/polynomialfunctions/RootCounting.h>

//#define VS_DEBUG_VARIABLE_VALUATIONS
//#define VS_DEBUG_VARIABLE_BOUNDS
//#define VS_DEBUG_LOCAL_CONFLICT_SEARCH
//#define VS_DEBUG_ROOTS_CHECK

//#define VS_LOG_INFSUBSETS

namespace smtrat {
namespace vs
{   
    State::State( carl::IDPool* _conditionIdAllocator, bool _withVariableBounds ):
        mConditionsSimplified( false ),
        mHasChildrenToInsert( false ),
        mHasRecentlyAddedConditions( false ),
        mInconsistent( false ),
        mMarkedAsDeleted( false ),
        mSubResultsSimplified( false ),
        mTakeSubResultCombAgain( false ),
        mTestCandidateCheckedForBounds( false ),
        mCannotBeSolved( false ),
        mCannotBeSolvedLazy( false ),
        mTryToRefreshIndex( false ),
        mBackendCallValuation( 0 ),
        mID( 0 ),
        mValuation( 0 ),
        mType( TEST_CANDIDATE_TO_GENERATE ),
        mIndex( carl::Variable::NO_VARIABLE ),
        mpOriginalCondition( NULL ),
        mpFather( NULL ),
        mpSubstitution( NULL ),
        mpSubstitutionResults( NULL ),
        mpSubResultCombination( NULL ),
        mpConditions( new ConditionList() ),
        mpConflictSets( new ConflictSets() ),
        mpChildren( new std::list< State* >() ),
        mpTooHighDegreeConditions( new carl::PointerSet<Condition>() ),
        mpVariableBounds( _withVariableBounds ? new VariableBoundsCond() : NULL ),
        mpInfinityChild( NULL ),
        mMinIntTestCanidate( Rational(1) ),
        mMaxIntTestCanidate( Rational(-1) ),
        mCurrentIntRange( 0 ),
        mpConditionIdAllocator( _conditionIdAllocator ),
        mRealVarVals(),
        mIntVarVals(),
        mBestVarVals()
        #ifdef SMTRAT_DEVOPTION_Statistics
        , mpStatistics( nullptr )
        #endif
    {}

    State::State( State* const _father, const Substitution& _substitution, carl::IDPool* _conditionIdAllocator, bool _withVariableBounds ):
        mConditionsSimplified( false ),
        mHasChildrenToInsert( false ),
        mHasRecentlyAddedConditions( false ),
        mInconsistent( false ),
        mMarkedAsDeleted( false ),
        mSubResultsSimplified( false ),
        mTakeSubResultCombAgain( false ),
        mTestCandidateCheckedForBounds( false ),
        mCannotBeSolved( false ),
        mCannotBeSolvedLazy( false ),
        mTryToRefreshIndex( false ),
        mBackendCallValuation( 0 ),
        mID( 0 ),
        mValuation( 0 ),
        mType( SUBSTITUTION_TO_APPLY ),
        mIndex( carl::Variable::NO_VARIABLE ),
        mpOriginalCondition( NULL ),
        mpFather( _father ),
        mpSubstitution( new Substitution( _substitution ) ),
        mpSubstitutionResults( NULL ),
        mpSubResultCombination( NULL ),
        mpConditions( new ConditionList() ),
        mpConflictSets( new ConflictSets() ),
        mpChildren( new std::list< State* >() ),
        mpTooHighDegreeConditions( new carl::PointerSet<Condition>() ),
        mpVariableBounds( _withVariableBounds ? new VariableBoundsCond() : NULL ),
        mpInfinityChild( NULL ),
        mMinIntTestCanidate( Rational(1) ),
        mMaxIntTestCanidate( Rational(-1) ),
        mCurrentIntRange( 0 ),
        mpConditionIdAllocator( _conditionIdAllocator ),
        mRealVarVals(),
        mIntVarVals(),
        mBestVarVals()
        #ifdef SMTRAT_DEVOPTION_Statistics
        , mpStatistics( nullptr )
        #endif
    {}

    State::~State()
    {
        mpTooHighDegreeConditions->clear();
        delete mpTooHighDegreeConditions;
        while( !mpConflictSets->empty() )
        {
            const Substitution* sub = mpConflictSets->begin()->first;
            mpConflictSets->erase( mpConflictSets->begin() );
            if( sub != NULL && sub->type() == Substitution::Type::INVALID )
            {
                delete sub;
            }
        }
        delete mpConflictSets;
        while( !children().empty() )
        {
            State* rpChild = rChildren().back();
            rChildren().pop_back();
            if( rpChild == mpInfinityChild ) mpInfinityChild = NULL;
            delete rpChild;
        }
        delete mpChildren;
        while( !conditions().empty() )
        {
            const Condition* pCond = rConditions().back();
            rConditions().pop_back();
            if( mpVariableBounds != NULL )
                mpVariableBounds->removeBound( pCond->constraint(), pCond );
            mpConditionIdAllocator->free( pCond->getId() );
            delete pCond;
            pCond = NULL;
        }
        if( mpVariableBounds != NULL )
            delete mpVariableBounds;
        delete mpConditions;
        if( mpSubstitution != NULL )
            delete mpSubstitution;
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
                        mpConditionIdAllocator->free( rpCond->getId() );
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
    
    void State::removeStatesFromRanking( const State& toRemove, ValuationMap& _ranking )
    {
        UnsignedTriple key = UnsignedTriple( toRemove.valuation(), std::pair<unsigned, unsigned>( toRemove.id(), toRemove.backendCallValuation() ) );
        _ranking.erase( key );
        for( const State* child : toRemove.children() )
            removeStatesFromRanking( *child, _ranking );
    }
    
    void State::resetCannotBeSolvedLazyFlags()
    {
        mCannotBeSolvedLazy = false;
        for( State* child : *mpChildren )
            child->resetCannotBeSolvedLazyFlags();
    }

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

    bool State::substitutionApplicable() const
    {
        auto cond = conditions().begin();
        while( cond != conditions().end() )
        {
            if( substitutionApplicable( (**cond).constraint() ) )
                return true;
            ++cond;
        }
        return false;
    }

    bool State::substitutionApplicable( const smtrat::ConstraintT& _constraint ) const
    {
        if( !isRoot() )
            if( _constraint.variables().has( substitution().variable() ))
                return true;
        return false;
    }

    bool State::hasNoninvolvedCondition() const
    {
        auto cond = conditions().begin();
        while( cond != conditions().end() )
        {
            if( (*cond)->flag() )
                ++cond;
            else
                return true;
        }
        return false;
    }
    
    bool State::allTestCandidatesInvalidated( const Condition* _condition ) const
    {
        if( !_condition->flag() || tooHighDegreeConditions().find( _condition ) != tooHighDegreeConditions().end() )
            return false;
        for( const State* child : children() )
        {
            if( child->substitution().originalConditions().find( _condition ) != child->substitution().originalConditions().end() && !child->isInconsistent() )
                return false;
        }
        return true;
    }

    bool State::hasChildWithID() const
    {
        auto child = children().begin();
        while( child != children().end() )
        {
            if( (*child)->id() == 0 )
                ++child;
            else
                return true;
        }
        return false;
    }
    
    bool State::containsState( const State* _state ) const
    {
        if( this == _state ) return true;
        for( const State* child : children() )
            if( child->containsState( _state ) )
                return true;
        return false;
    }

    bool State::hasOnlyInconsistentChildren() const
    {
        auto child = children().begin();
        while( child != children().end() )
        {
            if( (*child)->isInconsistent() )
                ++child;
            else
                return false;
        }
        return true;
    }

    bool State::occursInEquation( const carl::Variable& _variable ) const
    {
        for( auto cond = conditions().begin(); cond != conditions().end(); ++cond )
            if( (*cond)->constraint().relation() == carl::Relation::EQ && (*cond)->constraint().hasVariable( _variable ) )
                return true;
        return false;
    }

    bool State::hasFurtherUncheckedTestCandidates() const
    {
        if( children().size() > 1 )
            return true;
        else
        {
            for( auto cond = conditions().begin(); cond != conditions().end(); ++cond )
                if( !(**cond).flag() )
                    return true;
            return false;
        }
    }

    void State::variables( carl::Variables& _variables ) const
    {
        for( auto cond = conditions().begin(); cond != conditions().end(); ++cond ) {
			auto vars = (**cond).constraint().variables().underlyingVariables();
            _variables.insert( vars.begin(), vars.end() );
		}
    }

    unsigned State::numberOfNodes() const
    {
        unsigned result = 1;
        for( auto child = children().begin(); child != children().end(); ++child )
            result += (**child).numberOfNodes();
        return result;
    }

    State& State::root()
    {
        State* currentDT = this;
        while( !(*currentDT).isRoot() )
            currentDT = (*currentDT).pFather();
        return *currentDT;
    }
    
    bool State::getNextIntTestCandidate( smtrat::Rational& _nextIntTestCandidate, size_t _maxIntRange )
    {
        assert( _maxIntRange > 0 );
        assert( father().index().type() == carl::VariableType::VT_INT );
        assert( substitution().type() == Substitution::MINUS_INFINITY || substitution().type() == Substitution::PLUS_INFINITY );
        if( mCurrentIntRange >= _maxIntRange ) return false;
        if( substitution().type() == Substitution::MINUS_INFINITY )
        {
            _nextIntTestCandidate = father().minIntTestCandidate();
            --_nextIntTestCandidate;
        }
        else
        {
            _nextIntTestCandidate = father().maxIntTestCandidate();
            ++_nextIntTestCandidate;
        }
        assert( carl::isInteger( _nextIntTestCandidate ) );
        ++mCurrentIntRange;
        return true;
    }
    
    bool State::updateIntTestCandidates()
    {
        State* minusInfChild = NULL;
        State* plusInfChild = NULL;
        smtrat::Rational leastIntTc = 1;
        smtrat::Rational greatestIntTc = -1;
        for( auto child : rChildren() )
        {
            if( child->substitution().type() == Substitution::MINUS_INFINITY )
            {
                assert( minusInfChild == NULL );
                minusInfChild = child;
            }
            else if( child->substitution().type() == Substitution::PLUS_INFINITY )
            {
                assert( plusInfChild == NULL );
                plusInfChild = child;
            }
            else if( child->substitution().term().isInteger() )
            {
                smtrat::Rational currentTc = child->substitution().term().constantPart().constantPart();
                if( currentTc < mMinIntTestCanidate ) leastIntTc = currentTc;
                if( currentTc > mMaxIntTestCanidate ) greatestIntTc = currentTc;
            }
        }
        bool anythingChanged = false;
        if( leastIntTc != mMinIntTestCanidate )
        {
            mMinIntTestCanidate = leastIntTc;
            if( minusInfChild != NULL )
                minusInfChild->resetCurrentRangeSize();
            anythingChanged = true;
        }
        if( greatestIntTc != mMaxIntTestCanidate )
        {
            mMaxIntTestCanidate = greatestIntTc;
            if( plusInfChild != NULL )
                plusInfChild->resetCurrentRangeSize();
            anythingChanged = true;
        }
        return anythingChanged;
    }

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

    bool State::bestCondition( const Condition*& _bestCondition, size_t _numberOfAllVariables, bool _preferEquation )
    {
        auto cond = rConditions().begin();
        if( cond == conditions().end() )
            return false;
        assert( index() != carl::Variable::NO_VARIABLE );
        // Find the best condition.
        _bestCondition = *cond;
        ++cond;
        double bestConditionValuation    = _bestCondition->valuate( index(), _numberOfAllVariables, _preferEquation );
        double currentConditionValuation = 0;
        while( cond != conditions().end() )
        {
            if( !(**cond).flag() )
            {
                if( (*_bestCondition).flag() )
                {
                    _bestCondition         = *cond;
                    bestConditionValuation = _bestCondition->valuate( index(), _numberOfAllVariables, _preferEquation );
                }
                else
                {
                    currentConditionValuation = (**cond).valuate( index(), _numberOfAllVariables, _preferEquation );
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

    ConditionList::iterator State::constraintExists( const smtrat::ConstraintT& _constraint )
    {
        for( auto cond = rConditions().begin(); cond != conditions().end(); ++cond )
            if( (**cond).constraint() == _constraint )
                return cond;
        return rConditions().end();
    }

    void State::simplify( ValuationMap& _ranking )
    {
        if( !subResultsSimplified() )
        {
            if( hasSubstitutionResults() )
            {
                // If these conjunction together are consistent, simplify all conjunctions of
                // conditions in the remaining substitution results being disjunctions.
                unsigned subResultIndex  = 0;
                auto subResult = mpSubstitutionResults->begin();
                auto fixedConditions = mpSubstitutionResults->end();
                while( subResult != mpSubstitutionResults->end() )
                {
                    assert( !subResult->empty() );
                    auto condConjunction = subResult->begin();
                    bool containsEmptyCase = false;
                    while( condConjunction != subResult->end() && subResult->size() > 1 )
                    {
                        ConditionSetSet conflictingConditionPairs;
                        if( !simplify( condConjunction->first, conflictingConditionPairs, _ranking ) )
                        {
                            while( !condConjunction->first.empty() )
                            {
                                const Condition* rpCond = condConjunction->first.back();
                                condConjunction->first.pop_back();
                                mpConditionIdAllocator->free( rpCond->getId() );
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
                            auto subResComb = rSubResultCombination().begin();
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
                                mpConditionIdAllocator->free( rpCond->getId() );
                                delete rpCond;
                                rpCond = NULL;
                            }
                            subResult->pop_back();
                        }
                        subResult = mpSubstitutionResults->erase( subResult );
                        if( fixedPosWasEndBefore ) fixedConditions = mpSubstitutionResults->end();
                        if( hasSubResultsCombination() )
                        {
                            mTakeSubResultCombAgain = true;
                            assert( mpSubResultCombination->size() <= mpSubstitutionResults->size() );
                        }
                        else
                            mTakeSubResultCombAgain = false;
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
                                    auto subResComb = rSubResultCombination().begin();
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
                                if( hasSubResultsCombination() )
                                {
                                    mTakeSubResultCombAgain = true;
                                    assert( mpSubResultCombination->size() <= mpSubstitutionResults->size() );
                                }
                                else
                                    mTakeSubResultCombAgain = false;
                            }
                        }
                        else
                        {
                            ++subResult;
                            ++subResultIndex;
                        }
                    }
                }
            }
            mSubResultsSimplified = true;
        }
        // Simplify the condition vector.
        if( !conditionsSimplified() )
        {
            ConditionSetSet conflictingConditionPairs;
            if( !simplify( rConditions(), conflictingConditionPairs, _ranking, true ) )
            {
                addConflictSet( NULL, std::move(conflictingConditionPairs) );
                rInconsistent() = true;
            }
            mConditionsSimplified = true;
        }
    }

    bool State::simplify( ConditionList& _conditionVectorToSimplify, ConditionSetSet& _conflictSet, ValuationMap& _ranking, bool _stateConditions )
    {
        carl::PointerSet<Condition> redundantConditionSet;
        if( mpVariableBounds != NULL && _stateConditions && !mpVariableBounds->isConflicting() )
        {
            smtrat::EvalDoubleIntervalMap varIntervals = mpVariableBounds->getIntervalMap();
            for( auto iter = _conditionVectorToSimplify.begin(); iter != _conditionVectorToSimplify.end(); ++iter )
            {
                const smtrat::ConstraintT& constr = (*iter)->constraint();
                if( !constr.isBound() )
                {
                    carl::Relation stricterRelation = constr.relation();
                    switch( constr.consistentWith( varIntervals, stricterRelation ) )
                    {
                        case 0:
                        {
                            auto tmp = mpVariableBounds->getOriginsOfBounds( constr.variables().underlyingVariableSet() );
                            carl::PointerSet<Condition> condSet(tmp.begin(), tmp.end()); 
                            condSet.insert( *iter );
                            _conflictSet.insert( std::move( condSet ) );
                            break;
                        }
                        case 1:
                        {
                            redundantConditionSet.insert( *iter );
                            #ifdef SMTRAT_DEVOPTION_Statistics
                            mpStatistics->omittedConstraintByVB();
                            #endif
                            break;
                        }
                        default:
                        {
                            if( stricterRelation != constr.relation() )
                            {
                                auto tmp = mpVariableBounds->getOriginsOfBounds( constr.variables().underlyingVariableSet() );
                                carl::PointerSet<Condition> vbcondSet(tmp.begin(), tmp.end());
                                size_t nValuation = (*iter)->valuation();
                                bool nFlag = (*iter)->flag();
                                smtrat::ConstraintT nConstraint = smtrat::ConstraintT( constr.lhs(), stricterRelation );
                                unsigned nConstraintConsistency = nConstraint.isConsistent();
                                if( nConstraintConsistency == 2 )
                                {
                                    if( _stateConditions )
                                    {
                                        carl::PointerSet<Condition> oConds = (*iter)->originalConditions();
                                        for( const Condition* vbcond : vbcondSet )
                                            oConds.insert( vbcond->originalConditions().begin(), vbcond->originalConditions().end() );
                                        addCondition( nConstraint, oConds, nValuation, true, _ranking );
                                    }
                                    else
                                    {
                                        const Condition* cond = new Condition( nConstraint, mpConditionIdAllocator->get(), nValuation, nFlag, (*iter)->originalConditions(), true );
                                        for( const Condition* vbcond : vbcondSet )
                                            cond->pOriginalConditions()->insert( vbcond->originalConditions().begin(), vbcond->originalConditions().end() );
                                        _conditionVectorToSimplify.push_back( cond );
                                    }
                                    redundantConditionSet.insert( *iter );
                                }
                                else if( nConstraint.isConsistent() == 0 )
                                {
                                    auto tmp = mpVariableBounds->getOriginsOfBounds( constr.variables().underlyingVariableSet() );
                                    carl::PointerSet<Condition> condSet(tmp.begin(), tmp.end());
                                    condSet.insert( *iter );
                                    _conflictSet.insert( std::move( condSet ) );
                                }
                            }
                        }
                    }
                }
            }
        }
        if( _conditionVectorToSimplify.size() > 1 )
        {
            auto iterA = _conditionVectorToSimplify.begin();
            // Check all condition combinations.
            while( iterA != _conditionVectorToSimplify.end() )
            {
                auto iterB = iterA;
                ++iterB;
                while( iterB != _conditionVectorToSimplify.end() )
                {
                    const Condition* condA = *iterA;
                    const Condition* condB = *iterB;
                    signed strongProp = carl::compare<smtrat::Poly>( condA->constraint(), condB->constraint() );
                    // If the two conditions have the same solution space.
                    if( strongProp == 2 )
                    {
                        // Choose original conditions.
                        if( !condA->originalConditions().empty() &&!condB->originalConditions().empty() )
                        {
                            // If we have to choose which original conditions to take, choose those, which have been created earlier.
                            if( condB->valuation() < condA->valuation() )
                            {
                                *condA->pOriginalConditions() = carl::PointerSet<Condition>( condB->originalConditions() );
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
                        const smtrat::ConstraintT& constraintA = condA->constraint();
                        const smtrat::ConstraintT& constraintB = condB->constraint();
                        smtrat::ConstraintT nConstraint;
                        size_t nValuation = 0;
                        bool nFlag = false;
                        if( (constraintA.relation() == carl::Relation::GEQ && constraintB.relation() == carl::Relation::GEQ)
                                || (constraintA.relation() == carl::Relation::GEQ && constraintB.relation() == carl::Relation::LEQ)
                                || (constraintA.relation() == carl::Relation::LEQ && constraintB.relation() == carl::Relation::GEQ)
                                || (constraintA.relation() == carl::Relation::LEQ && constraintB.relation() == carl::Relation::LEQ) )
                        {
                            nConstraint = smtrat::ConstraintT( constraintB.lhs(), carl::Relation::EQ );
                            nValuation = condB->valuation();
                            nFlag = condB->flag();
                        }
                        else if( (constraintA.relation() == carl::Relation::NEQ && constraintB.relation() == carl::Relation::GEQ) )
                        {
                            nConstraint = smtrat::ConstraintT( constraintB.lhs(), carl::Relation::GREATER );
                            nValuation = condB->valuation();
                            nFlag = condB->flag();
                        }
                        else if( (constraintA.relation() == carl::Relation::GEQ && constraintB.relation() == carl::Relation::NEQ) )
                        {
                            nConstraint = smtrat::ConstraintT( constraintA.lhs(), carl::Relation::GREATER );
                            nValuation = condA->valuation();
                            nFlag = condA->flag();
                        }
                        else if( (constraintA.relation() == carl::Relation::NEQ && constraintB.relation() == carl::Relation::LEQ) )
                        {
                            nConstraint = smtrat::ConstraintT( constraintB.lhs(), carl::Relation::LESS );
                            nValuation = condB->valuation();
                            nFlag = condB->flag();
                        }
                        else if( (constraintA.relation() == carl::Relation::LEQ && constraintB.relation() == carl::Relation::NEQ) )
                        {
                            nConstraint = smtrat::ConstraintT( constraintA.lhs(), carl::Relation::LESS );
                            nValuation = condA->valuation();
                            nFlag = condA->flag();
                        }
                        else
                            assert( false );
                        unsigned nConstraintConsistency = nConstraint.isConsistent();
                        if( nConstraintConsistency == 2 )
                        {
                            if( _stateConditions )
                            {
                                carl::PointerSet<Condition> oConds = condB->originalConditions();
                                oConds.insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                                addCondition( nConstraint, oConds, nValuation, true, _ranking );
                            }
                            else
                            {
                                const Condition* cond = new Condition( nConstraint, mpConditionIdAllocator->get(), nValuation, nFlag, condB->originalConditions(), true );
                                cond->pOriginalConditions()->insert( condA->originalConditions().begin(), condA->originalConditions().end() );
                                _conditionVectorToSimplify.push_back( cond );
                            }
                            redundantConditionSet.insert( condA );
                            redundantConditionSet.insert( condB );
                        }
                        else if( nConstraint.isConsistent() == 0 )
                        {
                            carl::PointerSet<Condition> condSet;
                            condSet.insert( condA );
                            condSet.insert( condB );
                            _conflictSet.insert( condSet );
                        }
                    }
                    // If cond1's solution space is a superset of the solution space of cond2.
                    else if( strongProp == -1 )
                        redundantConditionSet.insert( condA );
                    // If it is easy to decide that cond1 and cond2 are conflicting.
                    else if( strongProp == -2 || strongProp == -4 )
                    {
                        carl::PointerSet<Condition> condSet;
                        condSet.insert( condA );
                        condSet.insert( condB );
                        _conflictSet.insert( condSet );
                    }
                    ++iterB;
                }
                ++iterA;
            }
            // Delete the conflicting conditions from redundant conditions.
            auto condSet = _conflictSet.begin();
            while( condSet != _conflictSet.end() )
            {
                auto cond = condSet->begin();
                while( cond != condSet->end() )
                {
                    redundantConditionSet.erase( *cond );
                    ++cond;
                }
                ++condSet;
            }
            if( _stateConditions )
                deleteConditions( redundantConditionSet, _ranking );
            else
            {
                // Delete the redundant conditions of the vector of conditions to simplify.
                auto cond = _conditionVectorToSimplify.begin();
                while( cond != _conditionVectorToSimplify.end() )
                {
                    auto iter = redundantConditionSet.find( *cond );
                    if( iter != redundantConditionSet.end() )
                    {
                        redundantConditionSet.erase( iter );
                        const Condition* toDel = *cond;
                        cond = _conditionVectorToSimplify.erase( cond );
                        mpConditionIdAllocator->free( toDel->getId() );
                        delete toDel;
                        toDel = NULL;
                    }
                    else
                        ++cond;
                }
            }
        }
        return _conflictSet.empty();
    }

    void State::setIndex( const carl::Variable& _index )
    {
        mIndex = _index;
        initConditionFlags();
    }

    void State::addConflictSet( const Substitution* _substitution, ConditionSetSet&& _condSetSet )
    {
        auto iter = mpConflictSets->find( _substitution );
        if( iter != mpConflictSets->end() )
        {
            iter->second.insert( std::move(_condSetSet) );
            if( _substitution != NULL && _substitution->type() == Substitution::Type::INVALID )
            {
                delete _substitution;
            }
        }
        else
        {
            ConditionSetSetSet condSetSetSet;
            condSetSetSet.insert( std::move(_condSetSet) );
            mpConflictSets->insert( std::pair<const Substitution*, ConditionSetSetSet>( _substitution, std::move(condSetSetSet) ) );
        }
        if( _substitution == NULL )
            rInconsistent() = true;
    }

    void State::addConflicts( const Substitution* _substitution, ConditionSetSet&& _condSetSet )
    {
        auto iter = mpConflictSets->find( _substitution );
        if( iter != mpConflictSets->end() )
        {
            ConditionSetSetSet newCondSetSetSet;
            for( auto condSetSet = iter->second.begin(); condSetSet != iter->second.end(); ++condSetSet )
            {
                ConditionSetSet newCondSetSet;
                newCondSetSet.insert( condSetSet->begin(), condSetSet->end() );
                newCondSetSet.insert( _condSetSet.begin(), _condSetSet.end() );
                newCondSetSetSet.insert( std::move(newCondSetSet) );
            }
            iter->second = std::move(newCondSetSetSet);
        }
        else
        {
            ConditionSetSetSet condSetSetSet;
            condSetSetSet.insert( std::move(_condSetSet) );
            mpConflictSets->insert( std::pair<const Substitution*, ConditionSetSetSet>( _substitution, std::move(condSetSetSet) ) );
        }
    }

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

    bool State::updateOCondsOfSubstitutions( const Substitution& _substitution, std::vector<State*>& _reactivatedStates )
    {
        for( auto child = rChildren().begin(); child != children().end(); ++child )
        {
            // TODO: If there is a child with a test candidate whose side conditions are a superset of the side conditions of the
            // given substitution, remove the child and add the test candidates original conditions to the original conditions of
            // the given substitution. However, when deleting later the original condition of the given substitution, the its
            // getting nasty.
            if( (**child).substitution() == _substitution )
            {
                if( index().type() == carl::VariableType::VT_INT && mpInfinityChild == *child )
                {
                    mpInfinityChild = NULL;
                    (**child).rSubstitution().rOriginalConditions().clear();
                }
                (**child).rSubstitution().rOriginalConditions().insert( _substitution.originalConditions().begin(), _substitution.originalConditions().end() );
                return true;
            }
            else if( index().type() == carl::VariableType::VT_INT && _substitution.term().isInteger() )
            {
                smtrat::Rational intTc = _substitution.term().constantPart().constantPart();
                if( (**child).substitution().type() == Substitution::MINUS_INFINITY )
                {
                    if( intTc < (mMinIntTestCanidate - Rational(1)) )
                    {
                        (**child).resetCurrentRangeSize();
                        _reactivatedStates.push_back( *child );
                    }
                }
                else if( (**child).substitution().type() == Substitution::PLUS_INFINITY )
                {
                    if( intTc > (mMaxIntTestCanidate + Rational(1)) )
                    {
                        (**child).resetCurrentRangeSize();
                        _reactivatedStates.push_back( *child );
                    }
                }
            }
        }
        return false;
    }

    void State::addSubstitutionResults( std::vector<DisjunctionOfConditionConjunctions>&& _disjunctionsOfCondConj )
    {
        // For each disjunction add a substitution result to the substitution results of this state.
        if( mpSubstitutionResults == NULL )
            mpSubstitutionResults = new SubstitutionResults();
        for( auto disjunction = _disjunctionsOfCondConj.begin(); disjunction != _disjunctionsOfCondConj.end(); ++disjunction )
        {
            mpSubstitutionResults->emplace_back();
            for( auto conjunction = disjunction->begin(); conjunction != disjunction->end(); ++conjunction )
                mpSubstitutionResults->back().push_back( std::pair<ConditionList, bool>( std::move(*conjunction), false ) );
        }
        // Mark this state as not yet simplified.
        mSubResultsSimplified = false;
        mCannotBeSolved = false;
        mMarkedAsDeleted = false;
        mType = COMBINE_SUBRESULTS;
    }

    bool State::extendSubResultCombination()
    {
        assert( subResultsSimplified() );
        if( mpSubResultCombination == NULL )
            mpSubResultCombination = new SubResultCombination();
        if( mpSubResultCombination->size() < mpSubstitutionResults->size() )
        {
            unsigned bestSubResultIndex = 0;
            bool notConsideredSubResultFound = false;
            unsigned subResultIndex = 0;
            while( subResultIndex < mpSubstitutionResults->size() )
            {
                // Set all flags of conjunctions of conditions in the substitution result to false.
                auto condConj = mpSubstitutionResults->at( subResultIndex ).begin();
                while( condConj != mpSubstitutionResults->at( subResultIndex ).end() )
                {
                    condConj->second = false;
                    ++condConj;
                }
                // Check whether the sub result has not yet been considered.
                bool subResultAlreadyConsidered = false;
                auto subResComb = mpSubResultCombination->begin();
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
                        if( mpSubstitutionResults->at( subResultIndex ).size() < mpSubstitutionResults->at( bestSubResultIndex ).size() )
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
            mpSubResultCombination->push_back( std::pair<unsigned, unsigned>( bestSubResultIndex, 0 ) );
            return true;
        }
        else
            return false;
    }

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

    size_t State::getNumberOfCurrentSubresultCombination() const
    {
        if( hasSubResultsCombination() )
        {
            if( mpSubResultCombination->size() == 1 )
            {
                return mpSubResultCombination->begin()->second;
            }
            else
            {
                // First compute the number of combinations being a prefix of the current substitution result combination.
                size_t numOfPrefixCombinations = 1;
                for( size_t pos = 0; pos < mpSubResultCombination->size()-1; ++pos )
                {
                    numOfPrefixCombinations *= mpSubstitutionResults->at( pos ).size();
                }
                size_t numOfCurrentCombination = 1;
                for( const auto& src : *mpSubResultCombination )
                {
                    numOfCurrentCombination *= src.second;
                }
                return numOfPrefixCombinations + numOfCurrentCombination;
            }
        }
        return 0;
    }

    ConditionList State::getCurrentSubresultCombination() const
    {
        ConditionList currentSubresultCombination;
        assert( hasSubResultsCombination() );
        auto iter = mpSubResultCombination->begin();
        while( iter != mpSubResultCombination->end() )
        {
            for( auto cond = mpSubstitutionResults->at( iter->first ).at( iter->second ).first.begin();
                    cond != mpSubstitutionResults->at( iter->first ).at( iter->second ).first.end(); ++cond )
            {
                currentSubresultCombination.push_back( new Condition( **cond, mpConditionIdAllocator->get() ) );
            }
            ++iter;
        }
        return currentSubresultCombination;
    }

    bool State::refreshConditions( ValuationMap& _ranking )
    {
        assert( type() == COMBINE_SUBRESULTS );
        bool conditionsChanged = false;
        if( !mpSubstitutionResults->empty() )
        {
            // Get the conditions of the currently considered combination of substitution results.
            ConditionList newCombination = getCurrentSubresultCombination();
            // Simplify the conditions already here, to avoid unnecessarily adding and deleting conditions.
            ConditionSetSet conflictingConditionPairs;
            if( !simplify( newCombination, conflictingConditionPairs, _ranking ) )
                rInconsistent() = true;
            // Delete the conditions of this combination, which do already occur in the considered conditions of this state.
            carl::PointerSet<Condition> condsToDelete;
            auto cond = rConditions().begin();
            while( cond != conditions().end() )
            {
                // Check if the condition occurs in the new combination. If so, delete
                // the corresponding condition in the new combination.
                bool condOccursInNewConds = false;
                auto newCond = newCombination.begin();
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
                                *(**cond).pOriginalConditions() = carl::PointerSet<Condition>( (**newCond).originalConditions() );
                                (**cond).rValuation()          = (**newCond).valuation();
                            }
                        }
                        else
                            (**cond).pOriginalConditions()->insert( (**newCond).originalConditions().begin(), (**newCond).originalConditions().end() );
                        const Condition* pCond = *newCond;
                        newCond = newCombination.erase( newCond );
                        mpConditionIdAllocator->free( pCond->getId() );
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
                }
                ++cond;
            }
            if( !newCombination.empty() )
                conditionsChanged = true;
            // Delete the conditions, which do not occur in the current combination.
            if( !condsToDelete.empty() )
            {
                conditionsChanged = true;
                deleteConditions( condsToDelete, _ranking );
            }
            // Add the remaining conditions of the current combination to the conditions this state considers.
            for( auto newCond = newCombination.begin(); newCond != newCombination.end(); ++newCond )
                addCondition( (**newCond).constraint(), (**newCond).originalConditions(), (**newCond).valuation(), true, _ranking );
            while( !newCombination.empty() )
            {
                const Condition* rpCond = newCombination.back();
                newCombination.pop_back();
                mpConditionIdAllocator->free( rpCond->getId() );
                delete rpCond; // TODO: this has to be done maybe in some situations or somewhere else
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

    void State::initConditionFlags()
    {
        assert( index() != carl::Variable::NO_VARIABLE );
        for( auto cond = rConditions().begin(); cond != conditions().end(); ++cond )
        {
            (**cond).rFlag() = !(**cond).constraint().hasVariable( index() );//  || (**cond).constraint().isUpperBound();
        }
    }

    bool State::initIndex( const carl::Variables& _allVariables, const smtrat::VariableValuationStrategy& _vvstrat, bool _preferEquation, bool _tryDifferentVarOrder, bool _useFixedVariableOrder )
    {
        assert( !_tryDifferentVarOrder || !mTryToRefreshIndex );
        if( conditions().empty() )
            return false;
        if( _allVariables.size() == 1 )
        {
            if( index() != *_allVariables.begin() )
            {
                setIndex( *_allVariables.begin() );
                return true;
            }
            return false;
        }
        if( _tryDifferentVarOrder )
        {
            if( mBestVarVals.empty() )
                return false;
            size_t bestVar = mBestVarVals.back();
            mBestVarVals.pop_back();
            std::vector<std::pair<carl::Variable, std::multiset<double>>>& varVals = mRealVarVals.empty() ? mIntVarVals : mRealVarVals;
            assert( index() != varVals[bestVar].first );
            setIndex( varVals[bestVar].first );
            return true;
        }
        mTryToRefreshIndex = false;
        mRealVarVals.clear();
        mIntVarVals.clear();
        for( auto var = _allVariables.begin(); var != _allVariables.end(); ++var )
        {
            if( var->type() == carl::VariableType::VT_INT )
                mIntVarVals.push_back( std::pair<carl::Variable, std::multiset<double> >( *var, std::multiset<double>() ) );
            else
                mRealVarVals.push_back( std::pair<carl::Variable, std::multiset<double> >( *var, std::multiset<double>() ) );
        }
        std::vector<std::pair<carl::Variable, std::multiset<double>>>& varValsB = mRealVarVals.empty() ? mIntVarVals : mRealVarVals;
        // Find for each variable the highest valuation of all conditions' constraints.
        for( auto cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            // Check for all variables their valuation for the given constraint.
            for( auto var = varValsB.begin(); var != varValsB.end(); ++var )
            {
                double varInConsVal = (**cond).valuate( var->first, _allVariables.size(), _preferEquation );
                if( varInConsVal != 0 )
                    var->second.insert( varInConsVal );
            }
        }
        std::vector<std::pair<carl::Variable, std::multiset<double>>>& varVals = mRealVarVals.empty() ? mIntVarVals : mRealVarVals;
        #ifdef VS_DEBUG_VARIABLE_VALUATIONS
        for( auto var = varVals.begin(); var != varVals.end(); ++var )
        {
            std::cout << var->first << ":  ";
            for( auto varVal = var->second.begin(); varVal != var->second.end(); ++varVal )
                std::cout <<  setprecision(10) << *varVal << " | ";
            std::cout << std::endl;
        }
        #endif
        // Find the variable which has in a constraint the best valuation. If more than one have the highest valuation, 
        // then choose the one having the higher valuation according to the order in _allVariables.
        if( _useFixedVariableOrder )
        {
            for( const auto& varValPair : varVals )
            {
                if( !varValPair.second.empty() )
                {   
                    if( index() != varValPair.first )
                    {
                        setIndex( varValPair.first );
                        return true;
                    }
                    return false;
                }
            }
            return false;
        }
        mBestVarVals.clear();
        switch( _vvstrat )
        {
            case smtrat::VariableValuationStrategy::OPTIMIZE_BEST:
                bestConstraintValuation( varVals );
                break;
            case smtrat::VariableValuationStrategy::OPTIMIZE_AVERAGE:
                averageConstraintValuation( varVals );
                break;
            default:
                assert( _vvstrat == smtrat::VariableValuationStrategy::OPTIMIZE_WORST );
                worstConstraintValuation( varVals );
                break;
        }
        assert( !mBestVarVals.empty() );
        size_t bestVar = mBestVarVals.back();
        mBestVarVals.pop_back();
        if( index() != varVals[bestVar].first )
        {
            setIndex( varVals[bestVar].first );
            return true;
        }
        return false;
    }
    
    void State::bestConstraintValuation( const std::vector<std::pair<carl::Variable, std::multiset<double>>>& _varVals )
    {
        assert( _varVals.size() > 1 );
        size_t var = 1;
        mBestVarVals.push_back(0);
        while( var < _varVals.size() )
        {
            const auto& vv = _varVals[var];
            const auto& bv = _varVals[mBestVarVals.back()];
            if( !vv.second.empty() && !bv.second.empty() )
            {
                if( vv.second.size() == 1 && bv.second.size() == 1 )
                {
                    if( *vv.second.begin() < *bv.second.begin() )
                    {
                        mBestVarVals.clear();
                        mBestVarVals.push_back(var);
                    }
                    else if( *vv.second.begin() == *bv.second.begin() )
                        mBestVarVals.push_back(var);
                }
                else
                {
                    auto varInConsVal = vv.second.begin();
                    auto bestVarInConsVal = bv.second.begin();
                    while( varInConsVal != vv.second.end() && bestVarInConsVal != bv.second.end() )
                    {
                        if( *varInConsVal < *bestVarInConsVal )
                        {
                            mBestVarVals.clear();
                            mBestVarVals.push_back(var);
                            break;
                        }
                        else if( *varInConsVal > *bestVarInConsVal )
                            break;
                        ++varInConsVal;
                        ++bestVarInConsVal;
                    }
                    if( varInConsVal == vv.second.end() )
                    {
                        if( bestVarInConsVal == bv.second.end() )
                            mBestVarVals.push_back(var);
                        else
                        {
                            mBestVarVals.clear();
                            mBestVarVals.push_back(var);
                        }
                    }
                }
            }
            else if( !vv.second.empty() && bv.second.empty() )
            {
                mBestVarVals.clear();
                mBestVarVals.push_back(var);
            }
            ++var;
        }
    }
    
    void State::averageConstraintValuation( const std::vector<std::pair<carl::Variable, std::multiset<double>>>& _varVals )
    {
        assert( _varVals.size() > 1 );
        std::size_t var = 0;
        mBestVarVals.push_back(0);
        double bestAvgVal = 0;
        const std::multiset<double>& vals = _varVals[var].second;
        if( !vals.empty() )
        {
			bestAvgVal = std::accumulate(vals.begin(), vals.end(), 0.0) / static_cast<double>(vals.size());
        }
        ++var;
        for(; var < _varVals.size(); ++var )
        {
            const std::multiset<double>& valsB = _varVals[var].second;
            if( !valsB.empty() )
            {
                double curAvgVal = std::accumulate(valsB.begin(), valsB.end(), 0.0) / static_cast<double>(valsB.size());
                if( curAvgVal > 0 && (bestAvgVal == 0 || curAvgVal < bestAvgVal) )
                {
                    mBestVarVals.clear();
                    mBestVarVals.push_back(var);
                }
                else if( curAvgVal == bestAvgVal )
                    mBestVarVals.push_back(var);
            }
        }
    }
    
    void State::worstConstraintValuation( const std::vector<std::pair<carl::Variable, std::multiset<double>>>& _varVals )
    {
        assert( _varVals.size() > 1 );
        size_t var = 1;
        mBestVarVals.push_back(0);
        while( var < _varVals.size() )
        {
            const auto& vv = _varVals[var];
            const auto& bv = _varVals[mBestVarVals.back()];
            if( !vv.second.empty() && !bv.second.empty() )
            {
                if( vv.second.size() == 1 && bv.second.size() == 1 )
                {
                    if( *vv.second.begin() < *bv.second.begin() )
                    {
                        mBestVarVals.clear();
                        mBestVarVals.push_back(var);
                    }
                    else if( *vv.second.begin() == *bv.second.begin() )
                        mBestVarVals.push_back(var);
                }
                else
                {
                    auto varInConsVal = vv.second.rbegin();
                    auto bestVarInConsVal = bv.second.rbegin();
                    while( varInConsVal != vv.second.rend() && bestVarInConsVal != bv.second.rend() )
                    {
                        if( *varInConsVal < *bestVarInConsVal )
                        {
                            mBestVarVals.clear();
                            mBestVarVals.push_back(var);
                            break;
                        }
                        else if( *varInConsVal > *bestVarInConsVal )
                            break;
                        ++varInConsVal;
                        ++bestVarInConsVal;
                    }
                    if( varInConsVal == vv.second.rend() )
                    {
                        if( bestVarInConsVal == bv.second.rend() )
                            mBestVarVals.push_back(var);
                        else
                        {
                            mBestVarVals.clear();
                            mBestVarVals.push_back(var);
                        }
                    }
                }
            }
            else if( !vv.second.empty() && bv.second.empty() )
            {
                mBestVarVals.clear();
                mBestVarVals.push_back(var);
            }
            ++var;
        }
    }

    void State::addCondition( const smtrat::ConstraintT& _constraint, const carl::PointerSet<Condition>& _originalConditions, size_t _valutation, bool _recentlyAdded, ValuationMap& _ranking )
    {
        // Check if the constraint is variable-free and consistent. If so, discard it.
        unsigned constraintConsistency = _constraint.isConsistent();
        assert( constraintConsistency != 0 );
        if( constraintConsistency != 1 )
        {
            // Check if the condition already exists.
            mConditionsSimplified = false;
            mCannotBeSolved       = false;
            mMarkedAsDeleted      = false;
            // The state is not a leaf.
            if( index() != carl::Variable::NO_VARIABLE )
            {
                if( _recentlyAdded )
                    mHasRecentlyAddedConditions = true;
                bool constraintWithFinitlyManySolutionCandidatesInIndexExists = false;
                for( auto child = children().begin(); child != children().end(); ++child )
                {
                    if( (**child).pOriginalCondition() != NULL )
                        constraintWithFinitlyManySolutionCandidatesInIndexExists = true;
                    break;
                }
                // Does the constraint contain the variable to eliminate.
                if( !_constraint.variables().has( index() )
                        || constraintWithFinitlyManySolutionCandidatesInIndexExists )
                {
                    rConditions().push_back( new Condition( _constraint, mpConditionIdAllocator->get(), _valutation, true, _originalConditions, _recentlyAdded ) );
                    if( mpVariableBounds != NULL && mpVariableBounds->addBound( _constraint, rConditions().back() ) )
                        mTestCandidateCheckedForBounds = false;
                }
                else
                {
                    if( mpInfinityChild != NULL )
                    {
                        removeStatesFromRanking( *mpInfinityChild, _ranking );
                        mpConflictSets->erase( mpInfinityChild->pSubstitution() );
                        mpChildren->remove( mpInfinityChild );
                        delete mpInfinityChild; // DELETE STATE
                        mpInfinityChild = NULL;
                    }
                    rConditions().push_back( new Condition( _constraint, mpConditionIdAllocator->get(), _valutation, false, _originalConditions, _recentlyAdded ) );
                    if( mpVariableBounds != NULL && mpVariableBounds->addBound( _constraint, rConditions().back() ) )
                        mTestCandidateCheckedForBounds = false;
                }
            }
            // The state is a leaf.
            else
            {
                assert( mpInfinityChild == NULL );
                rConditions().push_back( new Condition( _constraint, mpConditionIdAllocator->get(), _valutation, false, _originalConditions, false ) );
                if( mpVariableBounds != NULL && mpVariableBounds->addBound( _constraint, rConditions().back() ) )
                    mTestCandidateCheckedForBounds = false;
            }
        }
    }
    
    bool State::checkSubresultCombinations() const
    {
        if( hasSubstitutionResults() && hasSubResultsCombination() )
        {
            auto iter = mpSubResultCombination->begin();
            while( iter != mpSubResultCombination->end() )
            {
                if( iter->first >= mpSubstitutionResults->size() ) return false;
                if( iter->second >= mpSubstitutionResults->at( iter->first ).size() ) return false;
                ++iter;
            }
        }
        return true;
    }

    int State::deleteOrigins( carl::PointerSet<Condition>& _originsToDelete, ValuationMap& _ranking )
    {
        if( _originsToDelete.empty() ) return 1;
        if( !isRoot() )
        {
            // Check if the substitution has a condition to delete as original condition.
            for( auto condToDel = _originsToDelete.begin(); condToDel != _originsToDelete.end(); ++condToDel )
            {
                auto oCondInSub = rSubstitution().rOriginalConditions().begin();
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
        carl::PointerSet<Condition> deletedConditions;
        carl::PointerSet<Condition> originsToRemove;
        for( auto originToDelete = _originsToDelete.begin(); originToDelete != _originsToDelete.end(); ++originToDelete )
        {
            auto condition = rConditions().begin();
            while( condition != conditions().end() )
            {
                if( (*condition)->originalConditions().find( *originToDelete ) != (*condition)->originalConditions().end() )
                {
                    if( mpVariableBounds != NULL )
                    {
                        carl::Variable* changedVar;
                        unsigned boundRemoved = mpVariableBounds->removeBound( (*condition)->constraint(), *condition, changedVar );
                        if( boundRemoved == 2 )
                        {
                            for( auto condB = rConditions().begin(); condB != conditions().end(); ++condB )
                            {
                                if( (*condB)->constraint().variables().has( *changedVar ) )
                                {
                                    originsToRemove.insert( *condB );
                                    (*condB)->rRecentlyAdded() = true;
                                    recentlyAddedConditionLeft = true;
                                    if( index() != carl::Variable::NO_VARIABLE )
                                        (*condB)->rFlag() = !(*condB)->constraint().hasVariable( index() );
                                }
                            }
                            delete changedVar;
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
            mInconsistent = false;
            mHasRecentlyAddedConditions = recentlyAddedConditionLeft;
        }
        mCannotBeSolved    = false;
        mMarkedAsDeleted   = false;
        mTryToRefreshIndex = true;
        // Delete everything originated by it in all children of this state.
        deleteOriginsFromChildren( originsToRemove, _ranking );
        // Delete the conditions in the conflict sets which are originated by any of the given origins.
        deleteOriginsFromConflictSets( _originsToDelete, false );     
        // Delete the conditions.
        while( !deletedConditions.empty() )
        {
            const Condition* pCond = *deletedConditions.begin();
            deletedConditions.erase( deletedConditions.begin() );
            mpConditionIdAllocator->free( pCond->getId() );
            delete pCond;
            pCond = NULL;
        }
        // Delete all conditions in the substitution result which are originated by any of the 
        // given origins and adapt the currently considered substitution result combination.
        deleteOriginsFromSubstitutionResults( _originsToDelete );
        return 1;
    }

    void State::deleteConditions( carl::PointerSet<Condition>& _conditionsToDelete, ValuationMap& _ranking )
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
        std::vector<const Condition* > condsToDelete;
        carl::PointerSet<Condition> originsToRemove;
        for( auto cond = rConditions().begin(); cond != conditions().end(); )
        {
            // Delete the condition from the vector this state considers.
            if( _conditionsToDelete.find( *cond ) != _conditionsToDelete.end() )
            {
                if( mpVariableBounds != NULL )
                {
                    carl::Variable* changedVar;
                    unsigned boundRemoved = mpVariableBounds->removeBound( (*cond)->constraint(), *cond, changedVar );
                    if( boundRemoved == 2 )
                    {
                        for( auto condB = rConditions().begin(); condB != conditions().end(); ++condB )
                        {
                            if( (*condB)->constraint().variables().has( *changedVar ) )
                            {
                                originsToRemove.insert( *condB );
                                (*condB)->rRecentlyAdded() = true;
                                recentlyAddedConditionLeft = true;
                                if( index() != carl::Variable::NO_VARIABLE )
                                    (*condB)->rFlag() = !(*condB)->constraint().hasVariable( index() );
                            }
                        }
                        delete changedVar;
                    }
                }
                conditionDeleted = true;
                condsToDelete.push_back( *cond );
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
            mInconsistent = false;
            mHasRecentlyAddedConditions = recentlyAddedConditionLeft;
        }
        originsToRemove.insert( _conditionsToDelete.begin(), _conditionsToDelete.end() );
        // Delete everything originated by the given conditions in all children of this state.
        deleteOriginsFromChildren( originsToRemove, _ranking );
        // Delete the conditions from the conflict sets.
        deleteOriginsFromConflictSets( originsToRemove, true );
        while( !condsToDelete.empty() )
        {
            const Condition* condToDel = condsToDelete.back();
            condsToDelete.pop_back();
            mpConditionIdAllocator->free( condToDel->getId() );
            delete condToDel;
            condToDel = NULL;
        }
        mCannotBeSolved    = false;
        mMarkedAsDeleted   = false;
        mTryToRefreshIndex = true;
    }

    void State::deleteOriginsFromChildren( carl::PointerSet<Condition>& _originsToDelete, ValuationMap& _ranking )
    {
        bool childWithIntTcDeleted = false;
        auto child = rChildren().begin();
        while( child != children().end() )
        {
            int result = (*child)->deleteOrigins( _originsToDelete, _ranking );
            if( result < 0 )
                initConditionFlags();
            if( result < 1 )
            {
                if( index().type() == carl::VariableType::VT_INT && (*child)->substitution().type() != Substitution::MINUS_INFINITY 
                    && (*child)->substitution().type() != Substitution::PLUS_INFINITY && (*child)->substitution().term().isInteger() )
                {
                    childWithIntTcDeleted = true;
                }
                auto conflictSet = rConflictSets().find( (*child)->pSubstitution() );
                if( conflictSet != conflictSets().end() )
                    rConflictSets().erase( conflictSet );
                State* toDelete = *child;
                removeStatesFromRanking( *toDelete, _ranking );
                child = rChildren().erase( child );
                if( toDelete == mpInfinityChild ) mpInfinityChild = NULL;
                delete toDelete;  // DELETE STATE
            }
            else
                ++child;
        }
        if( childWithIntTcDeleted )
            updateIntTestCandidates();
    }

    void State::deleteOriginsFromConflictSets( carl::PointerSet<Condition>& _originsToDelete, bool _originsAreCurrentConditions )
    {
        auto conflictSet = mpConflictSets->begin();
        while( conflictSet != mpConflictSets->end() )
        {
            ConditionSetSetSet updatedCondSetSetSet;
            auto condSetSet = conflictSet->second.begin();
            bool emptyReasonOccured = false;
            while( condSetSet != conflictSet->second.end() )
            {
                ConditionSetSet updatedCondSetSet;
                auto condSet = condSetSet->begin();
                while( condSet != condSetSet->end() )
                {
                    carl::PointerSet<Condition> updatedCondSet;
                    auto cond = condSet->begin();
                    bool condToDelOccured = false;
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
                            auto condToDel = _originsToDelete.begin();
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
                if( mpVariableBounds != NULL && conflictSet->first != NULL && conflictSet->first->type() == Substitution::INVALID )
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
                        auto subResComb = (**child).rSubResultCombination().begin();
                        while( subResComb != (*child)->subResultCombination().end() )
                        {
                            subResComb->second = 0;
                            ++subResComb;
                        }
                    }
                    auto subResult = (*child)->rSubstitutionResults().begin();
                    while( subResult != (*child)->substitutionResults().end() )
                    {
                        auto condConj = subResult->begin();
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
                    if( (*child)->hasSubstitutionResults() && (*child)->hasSubResultsCombination() )
                    {
                        (*child)->rTakeSubResultCombAgain() = true;
                    }
                    else
                       (*child)->rTakeSubResultCombAgain() = false; 
                }
                (*child)->rInconsistent() = false;
            }
            ++child;
        }
    }

    void State::deleteOriginsFromSubstitutionResults( carl::PointerSet<Condition>& _originsToDelete )
    {
        if( hasSubstitutionResults() )
        {
            unsigned subResultIndex = 0;
            auto subResult = rSubstitutionResults().begin();
            while( subResult != substitutionResults().end() )
            {
                unsigned subResultConjunctionIndex = 0;
                auto condConj = subResult->begin();
                while( condConj != subResult->end() )
                {
                    ConditionList conditionsToAdd;
                    auto cond = condConj->first.begin();
                    while( cond != condConj->first.end() )
                    {
                        bool oCondsDeleted = false;
                        auto oCond = (**cond).pOriginalConditions()->begin();
                        while( oCond != (**cond).originalConditions().end() )
                        {
                            if( _originsToDelete.find( *oCond ) != _originsToDelete.end() )
                            {
                                (**cond).pOriginalConditions()->erase( oCond++ );
                                oCondsDeleted = true;
                            }
                            else
                                ++oCond;
                        }
                        if( oCondsDeleted )
                        {
                            oCond = (**cond).pOriginalConditions()->begin();
                            while( oCond != (**cond).originalConditions().end() )
                            {
                                carl::PointerSet<Condition> oConds;
                                oConds.insert( *oCond );
                                conditionsToAdd.push_back( new Condition( (**oCond).constraint(), mpConditionIdAllocator->get(), (**cond).valuation(), false, oConds ) );
                                ++oCond;
                            }
                            const Condition* rpCond = *cond;
                            cond             = condConj->first.erase( cond );
                            condConj->second = false;
                            mpConditionIdAllocator->free( rpCond->getId() );
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
                            auto subResComb = rSubResultCombination().begin();
                            while( subResComb != rSubResultCombination().end() && subResComb->first != subResultIndex )
                                ++subResComb;
                            if( subResComb != subResultCombination().end() )
                            {
                                // If the currently considered condition conjunction in the currently considered substitution result
                                // is part of the substitution result combination of this state.
                                if( subResComb->second == subResultConjunctionIndex )
                                    rSubResultCombination().erase( subResComb ); // Remove this entry of the substitution result combinations.
                                // If the currently considered condition conjunction in the currently considered substitution result
                                // is NOT part of the substitution result combination of this state, but another condition conjunction in
                                // the currently considered substitution result with higher index, decrease this index.
                                else if( subResComb->second > subResultConjunctionIndex )
                                    --(subResComb->second);
                            }
                            if( subResult->size() == 1 )
                            {
                                auto subResCombB = rSubResultCombination().begin();
                                while( subResCombB != subResultCombination().end() )
                                {
                                    if( subResCombB->first > subResultIndex )
                                        --(subResCombB->first);
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
                    subResult = rSubstitutionResults().erase( subResult );
                else
                {
                    ++subResult;
                    ++subResultIndex;
                }
            }
            if( hasSubResultsCombination() )
            {
                mTakeSubResultCombAgain = true;
            }
            else
            {
                mTakeSubResultCombAgain = false;
            }
        }
    }

    std::vector<State*> State::addChild( const Substitution& _substitution )
    {
        std::vector<State*> result;
        if( !updateOCondsOfSubstitutions( _substitution, result ) )
        {
            if( index().type() == carl::VariableType::VT_INT && _substitution.type() == Substitution::NORMAL && _substitution.term().isInteger() )
            {
                smtrat::Rational intTC = _substitution.term().constantPart().constantPart();
                if( intTC > mMaxIntTestCanidate )
                {
                    mMaxIntTestCanidate = intTC;
                }
                if( intTC < mMinIntTestCanidate )
                {
                    mMinIntTestCanidate = intTC;
                }
            }
            State* state = new State( this, _substitution, mpConditionIdAllocator, mpVariableBounds != NULL );
            #ifdef SMTRAT_DEVOPTION_Statistics
            state->setStatistics( mpStatistics );
            mpStatistics->createTestCandidate();
            #endif
            const smtrat::ConstraintsT& sideConds = _substitution.sideCondition();
            for( auto sideCond = sideConds.begin(); sideCond != sideConds.end(); ++sideCond )
            {
//                if( _substitution.variable().type() != carl::VariableType::VT_INT || sideCond->relation() != carl::Relation::NEQ )
//                {
                    std::vector<DisjunctionOfConditionConjunctions> subResults;
                    subResults.emplace_back();
                    subResults.back().emplace_back();
                    subResults.back().back().push_back( new Condition( *sideCond, mpConditionIdAllocator->get(), state->treeDepth(), false, _substitution.originalConditions(), false ) );
                    state->addSubstitutionResults( std::move(subResults) );
                    state->rType() = SUBSTITUTION_TO_APPLY;
//                }
//                else
//                {
//                    smtrat::ConstraintT denomPos = smtrat::ConstraintT( sideCond->lhs(), carl::Relation::GREATER );
//                    smtrat::ConstraintT denomNeg = smtrat::ConstraintT( sideCond->lhs(), carl::Relation::LESS );
//                    assert( denomPos != ConstraintT( false ) || denomNeg != ConstraintT( false ) );
//                    // add (p<0 or p>0) to the substitution results, with the constraint being p!=0
//                    if( denomPos != ConstraintT( true ) && denomNeg != ConstraintT( true ) )
//                    {
//                        DisjunctionOfConditionConjunctions cases;
//                        if( denomPos != ConstraintT( false ) )
//                        {
//                            cases.emplace_back();
//                            cases.back().push_back( new vs::Condition( denomPos, mpConditionIdAllocator->get(), state->treeDepth(), false, _substitution.originalConditions(), false ) );
//                        }
//                        if( denomNeg != ConstraintT( false ) )
//                        {
//                            cases.emplace_back()
//                            cases.back().push_back( new vs::Condition( denomNeg, mpConditionIdAllocator->get(), state->treeDepth(), false, _substitution.originalConditions(), false ) );
//                        }
//                        std::vector<DisjunctionOfConditionConjunctions> subResults;
//                        subResults.push_back( cases );
//                        state->addSubstitutionResults( std::move(subResults) );
//                        state->rType() = SUBSTITUTION_TO_APPLY;
//                    }
//                }
            }
            rChildren().push_back( state );
            result.push_back( state );
        }
        return result;
    }

    void State::updateValuation( bool _lazy )
    {
        if( _lazy )
            mValuation = 1;
        else
            mValuation = 0;
        if( mCannotBeSolved )
        {
            mValuation += 1;
            updateBackendCallValuation();
        }
        else
        {
            if( !isRoot() ) 
                mValuation += 100 * treeDepth() + 10 * substitution().valuate( substitution().variable().type() == carl::VariableType::VT_REAL );
            else 
                mValuation += 1;
            if( isInconsistent() ) 
                mValuation += 7;
            else if( hasRecentlyAddedConditions() ) 
                mValuation += 6;
            else if( type() == TEST_CANDIDATE_TO_GENERATE && conditions().empty() ) 
                mValuation += 5;
            else
            {
                if( type() == SUBSTITUTION_TO_APPLY ) 
                    mValuation += 3;
                else if( type() == TEST_CANDIDATE_TO_GENERATE ) 
                {
                    mValuation += 4;
                }   
                else 
                    mValuation += 3;
            }
        }
    }

    void State::updateBackendCallValuation()
    {
        carl::Variables occuringVars = carl::Variables();
        std::set<carl::Relation> relationSymbols = std::set<carl::Relation>();
        for( auto cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
			auto vars = (*cond)->constraint().variables().underlyingVariables();
            occuringVars.insert( vars.begin(), vars.end() );
            relationSymbols.insert( (*cond)->constraint().relation() );
        }
        mBackendCallValuation = 300000*occuringVars.size();
        if( relationSymbols.find( carl::Relation::EQ ) != relationSymbols.end() )
        {
            mBackendCallValuation += 200000;
        }
        else if( relationSymbols.find( carl::Relation::LEQ ) != relationSymbols.end() || relationSymbols.find( carl::Relation::GEQ ) != relationSymbols.end() )
        {
            mBackendCallValuation += 100000;
        }
        mBackendCallValuation += conditions().size();
    }

    void State::passConflictToFather( bool _checkConflictForSideCondition, bool _useBackjumping, bool _includeInconsistentTestCandidates )
    {
        assert( isInconsistent() );
        bool coverSetOCondsContainIndexOfFather = false;
        if( index().type() != carl::VariableType::VT_INT || !mpConflictSets->empty() )
        {
            // Determine a covering set of the conflict sets.
            carl::PointerSet<Condition> covSet;
            ConditionSetSetSet confSets;
            auto nullConfSet = rConflictSets().find( NULL );
            if( nullConfSet != conflictSets().end() && !_includeInconsistentTestCandidates )
            {
                confSets.insert( nullConfSet->second.begin(), nullConfSet->second.end() );
            }
            else
            {
                for( auto confSet = rConflictSets().begin(); confSet != conflictSets().end(); ++confSet )
                    confSets.insert( confSet->second.begin(), confSet->second.end() );
            }
            coveringSet( confSets, covSet, treeDepth() );
            #ifdef SMTRAT_DEVOPTION_Statistics
            mpStatistics->coveringSet( covSet.size(), conditions().size() );
            #endif
            #ifdef VS_LOG_INFSUBSETS
            smtrat::ConstraintsT constraints;
            for( auto cond = covSet.begin(); cond != covSet.end(); ++cond )
                constraints.insert( (**cond).constraint() );
            smtrat::Module::addAssumptionToCheck( constraints, false, "VSModule_IS_1" );
            #endif
            // Get the original conditions to the covering set.
            carl::PointerSet<Condition> coverSetOConds;
            bool sideConditionIsPartOfConflict = !_checkConflictForSideCondition || (pOriginalCondition() == NULL || originalCondition().constraint().relation() != carl::Relation::EQ);
            const smtrat::ConstraintsT& subsSideConds = substitution().sideCondition();
            for( auto cond = covSet.begin(); cond != covSet.end(); ++cond )
            {
                // Add the original conditions of the condition to the conflict set.
                if( !(**cond).originalConditions().empty() )
                {
                    auto oCond = (**cond).originalConditions().begin();
                    while( oCond != (**cond).originalConditions().end() )
                    {
                        assert( father().index() != carl::Variable::NO_VARIABLE );
                        if( (**oCond).constraint().hasVariable( father().index() ) )
                            coverSetOCondsContainIndexOfFather = true;
                        coverSetOConds.insert( *oCond );
                        oCond++;
                    }
                }
                sideConditionIsPartOfConflict |= subsSideConds.find( (*cond)->constraint() ) != subsSideConds.end();
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
            ConditionSetSet conflictSet;
            assert( !coverSetOConds.empty() );
            conflictSet.insert( std::move(coverSetOConds) );
            // Add the original conditions of the covering set as a conflict set to the father.
            if( _useBackjumping || coverSetOCondsContainIndexOfFather )
                rFather().addConflictSet( pSubstitution(), std::move(conflictSet) );
            else
            {
                #ifdef SMTRAT_DEVOPTION_Statistics
                mpStatistics->backjumping( numberOfUnusedConditions() );
                #endif
                rFather().addConflictSet( NULL, std::move(conflictSet) );
            }
            // Delete the conflict sets.
            mpConflictSets->clear();
        }
        // Delete all children, the conflict sets and the conditions of this state.
        while( !children().empty() )
        {
            State* toDelete = rChildren().back();
            rChildren().pop_back();
            if( toDelete == mpInfinityChild ) mpInfinityChild = NULL;
            delete toDelete;
        }
        mpTooHighDegreeConditions->clear();
        while( !conditions().empty() )
        {
            const Condition* pCond = rConditions().back();
            rConditions().pop_back();
            if( mpVariableBounds != NULL )
                mpVariableBounds->removeBound( pCond->constraint(), pCond );
            mpConditionIdAllocator->free( pCond->getId() );
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
            rType() = COMBINE_SUBRESULTS;
        }
    }
 
    bool State::hasLocalConflict()
    {
        if( conflictSets().empty() || !tooHighDegreeConditions().empty() || !hasOnlyInconsistentChildren() ) return false;
        #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
        printAlone();
        #endif
        // Construct the local conflict consisting of all of the currently considered conditions,
        // which have been considered for test candidate construction.
        carl::PointerSet<Condition> localConflictSet;
        for( auto cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            if( (*cond)->flag() ) localConflictSet.insert( *cond );
        }
        // Check whether the local conflict set covers for each test candidate, its conditions have generated,
        // one of its conflict sets.
        #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
        std::cout << "local conflict:   { ";
        for( auto iter = localConflictSet.begin(); iter != localConflictSet.end(); ++iter )
            std::cout << (*iter)->constraint() << " ";
        std::cout << "}" << std::endl;
        #endif
        carl::PointerSet<Condition> infSubset;
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
                    std::cout << "covers:   { ";
                    for( auto iter = condSet->begin(); iter != condSet->end(); ++iter )
                        std::cout << (*iter)->constraint() << " ";
                    std::cout << "}  ??";
                    #endif
                    while( condA != condSet->end() &&  condB != localConflictSet.end() )
                    {
                        if( (*condB) < (*condA) )
                            ++condB;
                        else if( (*condA) < (*condB) )
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
                        std::cout << "   Yes!" << std::endl;
                        #endif
                        break;
                    }
                    else
                    {
                        #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
                        std::cout << "   No!" << std::endl;
                        #endif
                    }
                }
                if( condSet == condSetSet->end() )
                {
                    #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
                    std::cout << "No conflict set in conflict is covered!" << std::endl;
                    #endif
                    return false;
                }
                #ifdef VS_DEBUG_LOCAL_CONFLICT_SEARCH
                else
                {
                    std::cout << "A conflict set in conflict is covered!" << std::endl;
                }
                #endif
            }
        }
        if( containsConflictToCover )
        {
            ConditionSetSet localConflict;
            localConflict.insert( infSubset );
            addConflictSet( NULL, std::move(localConflict) );
            #ifdef SMTRAT_DEVOPTION_Statistics
            mpStatistics->localConflict( numberOfUnusedConditions() );
            #endif
            return true;
        }
        else
            return false;
    }

    bool State::checkTestCandidatesForBounds()
    {
        if( mTestCandidateCheckedForBounds ) return true;
        mTestCandidateCheckedForBounds = true;
        if( !isRoot() )
        {
            if( substitution().type() == Substitution::MINUS_INFINITY || substitution().type() == Substitution::PLUS_INFINITY ) return true;
            #ifdef VS_DEBUG_VARIABLE_BOUNDS
            std::cout << ">>> Check test candidate  " << substitution() << "  against:" << std::endl;
            father().variableBounds().print( std::cout, ">>>    " );
            #endif
            carl::PointerSet<Condition> conflict;
            std::vector< smtrat::DoubleInterval > solutionSpaces = solutionSpace( conflict );
            if( solutionSpaces.empty() )
            {
                ConditionSetSet conflicts;
                conflicts.insert( std::move(conflict) );
                pFather()->addConflictSet( pSubstitution(), std::move(conflicts) );
                #ifdef SMTRAT_DEVOPTION_Statistics
                mpStatistics->omittedTestCandidateWithVB( numberOfUnusedConditions() );
                #endif
                return false;
            }
        }
        return true;
    }

    std::vector< smtrat::DoubleInterval > State::solutionSpace( carl::PointerSet<Condition>& _conflictReason ) const
    {
        std::vector< smtrat::DoubleInterval > result;
        assert( !isRoot() );
        if( substitution().type() == Substitution::MINUS_INFINITY )
        {
            if( father().variableBounds().getDoubleInterval( substitution().variable() ).lowerBoundType() == carl::BoundType::INFTY )
                result.push_back( smtrat::DoubleInterval::unboundedInterval() );
            else
            {
                auto conflictBounds = father().variableBounds().getOriginsOfBounds( substitution().variable() );
                _conflictReason.insert( conflictBounds.begin(), conflictBounds.end() );
            }
            return result;
        }
        else if( substitution().type() == Substitution::PLUS_INFINITY )
        {
            if( father().variableBounds().getDoubleInterval( substitution().variable() ).upperBoundType() == carl::BoundType::INFTY )
                result.push_back( smtrat::DoubleInterval::unboundedInterval() );
            else
            {
                auto conflictBounds = father().variableBounds().getOriginsOfBounds( substitution().variable() );
                assert( !conflictBounds.empty() );
                _conflictReason.insert( conflictBounds.begin(), conflictBounds.end() );
            }
            return result;
        }
        else
        {
            smtrat::EvalDoubleIntervalMap intervals = father().variableBounds().getIntervalMap();
            smtrat::DoubleInterval solutionSpaceConst = carl::IntervalEvaluation::evaluate( substitution().term().constantPart(), intervals );
            smtrat::DoubleInterval solutionSpaceFactor = carl::IntervalEvaluation::evaluate( substitution().term().factor(), intervals );
            smtrat::DoubleInterval solutionSpaceRadicand = carl::IntervalEvaluation::evaluate( substitution().term().radicand(), intervals );
            smtrat::DoubleInterval solutionSpaceSqrt = carl::sqrt(solutionSpaceRadicand);
            smtrat::DoubleInterval solutionSpaceDenom = carl::IntervalEvaluation::evaluate( substitution().term().denominator(), intervals );
            smtrat::DoubleInterval solutionSpace = solutionSpaceFactor * solutionSpaceSqrt;
            solutionSpace = solutionSpace + solutionSpaceConst;
            #ifdef VS_DEBUG_VARIABLE_BOUNDS
            std::cout << ">>> Results in:" << std::endl;
            std::cout << ">>>    constant part      : " << solutionSpaceConst << std::endl;
            std::cout << ">>>    factor part        : " << solutionSpaceFactor << std::endl;
            std::cout << ">>>    radicand part      : " << solutionSpaceRadicand << std::endl;
            std::cout << ">>>    square root part   : " << solutionSpaceSqrt << std::endl;
            std::cout << ">>>    denominator part   : " << solutionSpaceDenom << std::endl;
            std::cout << ">>>    numerator part     : " << solutionSpace << std::endl;
            #endif
            smtrat::DoubleInterval resA;
            smtrat::DoubleInterval resB;
            bool splitOccurred = solutionSpace.div_ext( solutionSpaceDenom, resA, resB );
            const smtrat::DoubleInterval& subVarInterval = intervals[substitution().variable()];
            if( substitution().type() == Substitution::PLUS_EPSILON && resA.lowerBoundType() != carl::BoundType::INFTY )
            {
                if( resA.upperBoundType() == carl::BoundType::INFTY || resA.upper() == DBL_MAX )
                {
                    resA = smtrat::DoubleInterval( resA.lower(), carl::BoundType::STRICT, (double)0, carl::BoundType::INFTY );
                    if( splitOccurred )
                        resB = smtrat::DoubleInterval( resB.lower(), carl::BoundType::STRICT, (double)0, carl::BoundType::INFTY );
                }
                else
                {
                    resA = smtrat::DoubleInterval( resA.lower(), carl::BoundType::STRICT, std::nextafter( resA.upper(), INFINITY ), carl::BoundType::WEAK );
                    if( splitOccurred )
                        resB = smtrat::DoubleInterval( resB.lower(), carl::BoundType::STRICT, std::nextafter( resB.upper(), INFINITY ), carl::BoundType::WEAK );
                }
            }
            #ifdef VS_DEBUG_VARIABLE_BOUNDS
            std::cout << ">>>    division part 1    : " << std::setprecision(100) << resA << std::endl;
            std::cout << ">>>    subVarInterval     : " << std::setprecision(100) << subVarInterval << std::endl;
            #endif
            resA = carl::set_intersection(resA, subVarInterval);
            #ifdef VS_DEBUG_VARIABLE_BOUNDS
            std::cout << ">>>    intersection part 1: " << std::setprecision(100) << resA << std::endl;
            #endif
            if( !resA.isEmpty() )
                result.push_back( resA );
            if( splitOccurred )
            {
                #ifdef VS_DEBUG_VARIABLE_BOUNDS
                std::cout << ">>>    division part 2: " << resB << std::endl;
                #endif
                resB = carl::set_intersection(resB, subVarInterval );
                #ifdef VS_DEBUG_VARIABLE_BOUNDS
                std::cout << ">>>    intersection part 1: " << resB << std::endl;
                #endif
                if( !resB.isEmpty() )
                    result.push_back( resB );
            }
            if( result.empty() )
            {
                carl::Variables conflictVars = substitution().termVariables();
                conflictVars.insert( substitution().variable() );
                auto conflictBounds = father().variableBounds().getOriginsOfBounds( conflictVars );
                _conflictReason.insert( conflictBounds.begin(), conflictBounds.end() );
                _conflictReason.insert( substitution().originalConditions().begin(), substitution().originalConditions().end() );
            }
        }
        return result;
    }

    bool State::hasRootsInVariableBounds( const Condition* _condition, bool _useSturmSequence )
    {
        #ifdef VS_DEBUG_ROOTS_CHECK
        std::cout << __func__ << ":  " << _condition->constraint() << std::endl;
        #endif
        assert( index() != carl::Variable::NO_VARIABLE );
        const smtrat::ConstraintT& cons = _condition->constraint();
        smtrat::EvalDoubleIntervalMap intervals;
        if( cons.lhs().isUnivariate() )
        {
            smtrat::DoubleInterval varDomain = variableBounds().getDoubleInterval( index() );
            smtrat::Rational cb = carl::cauchyBound(carl::to_univariate_polynomial(cons.lhs()));
            #ifdef VS_DEBUG_ROOTS_CHECK
            std::cout << "Cauchy bound of  " << cons.lhs() << "  is  " << cb << "." << std::endl;
            #endif
            smtrat::DoubleInterval cbInterval = smtrat::DoubleInterval( smtrat::Rational(-cb), carl::BoundType::STRICT, cb, carl::BoundType::STRICT );
            varDomain = carl::set_intersection(varDomain, cbInterval );
            #ifdef VS_DEBUG_ROOTS_CHECK
            std::cout << varDomain << std::endl;
            #endif
            intervals[index()] = varDomain;
        }
        else
            intervals = variableBounds().getIntervalMap();
        carl::Relation rel = cons.relation();
        if( rel == carl::Relation::GREATER || rel == carl::Relation::LESS || rel == carl::Relation::NEQ )
        {
            auto indexDomain = intervals.find( index() );
            if( indexDomain->second.lowerBoundType() == carl::BoundType::STRICT )
                indexDomain->second.setLowerBoundType( carl::BoundType::WEAK );
        }
        smtrat::DoubleInterval solutionSpace = carl::IntervalEvaluation::evaluate( cons.lhs(), intervals );
        // TODO: if the condition is an equation and the degree in the index less than 3, 
        // then it is maybe better to consider the according test candidates
        #ifdef VS_DEBUG_ROOTS_CHECK
        std::cout << "solutionSpace: " << solutionSpace << std::endl;
        #endif
        if( solutionSpace.contains( 0 ) )
        {
            if( _useSturmSequence && cons.variables().size() == 1 ) // TODO: fails when having a multiple root at the boundary of the given interval for ss-computation
            {
                carl::UnivariatePolynomial<smtrat::Rational> rup = carl::to_univariate_polynomial(cons.lhs());
                auto seq = carl::sturm_sequence(rup);
                smtrat::Rational leftBound = carl::rationalize<smtrat::Rational>( intervals.begin()->second.lower() );
                smtrat::Rational rightBound = carl::rationalize<smtrat::Rational>( intervals.begin()->second.upper() );
                smtrat::RationalInterval interv( leftBound, carl::BoundType::WEAK, rightBound, carl::BoundType::WEAK );
                int numberOfRoots = carl::count_real_roots( seq, interv );
                assert( index() != carl::Variable::NO_VARIABLE );
                smtrat::Rational imageOfLeftBound = rup.evaluate( leftBound );
                smtrat::Rational imageOfRightBound = rup.evaluate( rightBound );
                if( imageOfLeftBound == Rational(0) )
                    ++numberOfRoots;
                if( imageOfRightBound == Rational(0) )
                {
                    if( intervals.begin()->second.upperBoundType() == carl::BoundType::STRICT && numberOfRoots != 0 )
                        --numberOfRoots;
                    if( intervals.begin()->second.upperBoundType() == carl::BoundType::WEAK )
                        ++numberOfRoots;
                }
                #ifdef VS_DEBUG_ROOTS_CHECK
                std::cout << "Image of left bound                     : " << imageOfLeftBound << std::endl;
                std::cout << "Image of right bound                    : " << imageOfRightBound << std::endl;
                std::cout << "Number of roots according sturm sequence: " << numberOfRoots << std::endl;
                #endif
                bool constraintInconsistent = false;
                if( numberOfRoots == 0 )
                {
                    if( cons.relation() == carl::Relation::EQ )
                        constraintInconsistent = true;
                    else if( imageOfLeftBound > 0 && (cons.relation() == carl::Relation::LESS || cons.relation() == carl::Relation::LEQ) )
                        constraintInconsistent = true;
                    else if( imageOfLeftBound < 0 && (cons.relation() == carl::Relation::GREATER || cons.relation() == carl::Relation::GEQ) )
                        constraintInconsistent = true;
                }
                else if( numberOfRoots == 1 )
                {
                    if( imageOfLeftBound > Rational(0) && imageOfRightBound > Rational(0) && cons.relation() == carl::Relation::LESS )
                        constraintInconsistent = true;
                    if( imageOfLeftBound < Rational(0) && imageOfRightBound < Rational(0) && cons.relation() == carl::Relation::GREATER )
                        constraintInconsistent = true;
                }
                if( constraintInconsistent )
                {
                    carl::PointerSet<Condition> origins;
                    origins.insert( _condition );
                    auto conflictingBounds = variableBounds().getOriginsOfBounds( index() );
                    origins.insert( conflictingBounds.begin(), conflictingBounds.end() );
                    ConditionSetSet conflicts;
                    conflicts.insert( std::move(origins) );
                    addConflictSet( NULL, std::move(conflicts) );
                    rInconsistent() = true;
                    #ifdef VS_DEBUG_ROOTS_CHECK
                    std::cout << "  -> false (1)" << std::endl;
                    #endif
                    return false;
                }
                if( numberOfRoots > 0 )
                {
                #ifdef VS_DEBUG_ROOTS_CHECK
                std::cout << "  -> true (1)" << std::endl;
                #endif
                return true;
                }
            }
            else
            {
                #ifdef VS_DEBUG_ROOTS_CHECK
                std::cout << "  -> true (3)" << std::endl;
                #endif
                return true;
            }
        }
        bool constraintInconsistent = false;
        if( cons.relation() == carl::Relation::EQ )
            constraintInconsistent = true;
        else if( solutionSpace.lower() > 0 && cons.relation() == carl::Relation::LEQ )
            constraintInconsistent = true;
        else if( solutionSpace.upper() < 0 && cons.relation() == carl::Relation::GEQ )
            constraintInconsistent = true;
        else if( solutionSpace.lower() >= 0 && cons.relation() == carl::Relation::LESS )
            constraintInconsistent = true;
        else if( solutionSpace.upper() <= 0 && cons.relation() == carl::Relation::GREATER )
            constraintInconsistent = true;
        carl::PointerSet<Condition> origins;
        origins.insert( _condition );
        auto conflictingBounds = variableBounds().getOriginsOfBounds( cons.variables().underlyingVariableSet() );
        origins.insert( conflictingBounds.begin(), conflictingBounds.end() );
        ConditionSetSet conflicts;
        conflicts.insert( std::move(origins) );
        Substitution* sub = NULL;
        if( !constraintInconsistent )
        {
            smtrat::ConstraintsT constraints;
            constraints.insert( _condition->constraint() );
            carl::PointerSet<Condition> subsOrigins;
            subsOrigins.insert( _condition );
            sub = new Substitution( index(), Substitution::INVALID, std::move(subsOrigins), std::move(constraints) );
        }
        addConflictSet( sub, std::move(conflicts) );
        #ifdef VS_DEBUG_ROOTS_CHECK
        std::cout << "  -> false (2)" << std::endl;
        #endif
        return false;
    }
    
    #ifdef VS_STATE_DEBUG_METHODS

    void State::print( const std::string _initiation, std::ostream& _out ) const
    {
        printAlone( _initiation, _out );
        _out << _initiation << "   " << "Children:" << std::endl;
        if( !children().empty() )
            for( auto child = children().begin(); child != children().end(); ++child )
                (**child).print( _initiation + "      ", _out );
        else _out << _initiation << "      no" << std::endl;
    }

    void State::printAlone( const std::string _initiation, std::ostream& _out ) const
    {
        _out << _initiation << "   State: (                     reference: " << this << std::endl;
        _out << _initiation << "                                valuation: " << valuation() << std::endl;
        _out << _initiation << "                                       ID: " << mID << std::endl;
        switch( type() )
        {
            case COMBINE_SUBRESULTS:
                _out << _initiation << "                               state type: COMBINE_SUBRESULTS" << std::endl;
                break;
            case SUBSTITUTION_TO_APPLY:
                _out << _initiation << "                               state type: SUBSTITUTION_TO_APPLY" << std::endl;
                break;
            case TEST_CANDIDATE_TO_GENERATE:
                _out << _initiation << "                               state type: TEST_CANDIDATE_TO_GENERATE" << std::endl;
                break;
            default:
                _out << _initiation << "                               state type: Undefined" << std::endl;
                break;
        }
        if( hasRecentlyAddedConditions() ) 
            _out << _initiation << "               hasRecentlyAddedConditions: yes" << std::endl;
        else 
            _out << _initiation << "               hasRecentlyAddedConditions: no" << std::endl;
        if( isInconsistent() ) 
            _out << _initiation << "                           isInconsistent: yes" << std::endl;
        else
            _out << _initiation << "                           isInconsistent: no" << std::endl;
        if( cannotBeSolved(false) )
            _out << _initiation << "                           cannotBeSolved: yes" << std::endl;
        else
            _out << _initiation << "                           cannotBeSolved: no" << std::endl;
        if( conditionsSimplified() )
            _out << _initiation << "                     conditionsSimplified: yes" << std::endl;
        else
            _out << _initiation << "                     conditionsSimplified: no" << std::endl;
        if( subResultsSimplified() )
            _out << _initiation << "                     subResultsSimplified: yes" << std::endl;
        else
            _out << _initiation << "                     subResultsSimplified: no" << std::endl;
        if( takeSubResultCombAgain() )
            _out << _initiation << "                   takeSubResultCombAgain: yes" << std::endl;
        else
            _out << _initiation << "                   takeSubResultCombAgain: no" << std::endl;
        if( tryToRefreshIndex() )
            _out << _initiation << "                        tryToRefreshIndex: yes" << std::endl;
        else
            _out << _initiation << "                        tryToRefreshIndex: no" << std::endl;
        if( mCannotBeSolved )
            _out << _initiation << "                             toHighDegree: yes" << std::endl;
        else
            _out << _initiation << "                             toHighDegree: no" << std::endl;
        if( markedAsDeleted() )
            _out << _initiation << "                          markedAsDeleted: yes" << std::endl;
        else
            _out << _initiation << "                          markedAsDeleted: no" << std::endl;
        if( pOriginalCondition() != NULL )
        {
            _out << _initiation << "                       original condition: ";
            _out << originalCondition().constraint() << " [";
            _out << pOriginalCondition() << "]" << std::endl;
        }
        if( mpInfinityChild != NULL )
        {
            _out << _initiation << "                           infinity child: " << mpInfinityChild << std::endl;
        }
        _out << _initiation << "                                    index: " << index() << " " << index().type() << "  )" << std::endl;
        printConditions( _initiation + "   ", _out );
        if( !isRoot() )
        {
            _out << _initiation + "   " << "Substitution: ";
            substitution().print( false, false, _out );
        }
        printSubstitutionResults( _initiation + "   ", _out );
        _out << _initiation << std::endl;
        printSubstitutionResultCombination( _initiation + "   ", _out );
        _out << _initiation << std::endl;
        printConflictSets( _initiation + "   ", _out );
        if( mpVariableBounds != NULL )
        {
            _out << _initiation << std::endl;
            mpVariableBounds->print( _out, _initiation );
            _out << _initiation << std::endl;
        }
    }

    void State::printConditions( const std::string _initiation, std::ostream& _out, bool _onlyAsConstraints ) const
    {
        _out << _initiation << "Condititons:" << std::endl;
        for( auto cond = conditions().begin(); cond != conditions().end(); ++cond )
        {
            _out << _initiation << "   ";
            if( _onlyAsConstraints )
                _out << (**cond).constraint();
            else 
                (**cond).print( _out );
            _out << std::endl;
        }
    }

    void State::printSubstitutionResults( const std::string _initiation, std::ostream& _out ) const
    {
        if( hasSubstitutionResults() )
        {
            for( auto subResult = mpSubstitutionResults->begin(); subResult != mpSubstitutionResults->end(); ++subResult )
            {
                if( subResult == mpSubstitutionResults->begin() )
                    _out << _initiation << "       [ ";
                else
                    _out << _initiation << "   and [ ";
                for( auto condConjunction = subResult->begin(); condConjunction != subResult->end(); ++condConjunction )
                {
                    if( condConjunction == subResult->begin() )
                        _out << "   ( ";
                    else
                        _out << _initiation << "         or ( ";

                    for( auto cond = condConjunction->first.begin(); cond != condConjunction->first.end(); ++cond )
                    {
                        if( cond != condConjunction->first.begin() ) _out << " and ";
                        std::cout << (*cond)->constraint();
                    }
                    _out << " )";
                    auto nextCondConjunction = condConjunction;
                    ++nextCondConjunction;
                    if( nextCondConjunction != subResult->end() ) _out << std::endl;
                }
                _out << " ]" << std::endl;
            }
        }
    }

    void State::printSubstitutionResultCombination( const std::string _initiation, std::ostream& _out ) const
    {
        if( hasSubstitutionResults() )
        {
            if( hasSubResultsCombination() )
            {
                _out << _initiation << "Substitution result combination:" << std::endl;
                for( auto subResComb = mpSubResultCombination->begin(); subResComb != mpSubResultCombination->end(); ++subResComb )
                {
                    _out << _initiation << "   (  ";
                    for( auto cond = mpSubstitutionResults->at( subResComb->first ).at( subResComb->second ).first.begin();
                            cond != mpSubstitutionResults->at( subResComb->first ).at( subResComb->second ).first.end(); ++cond )
                    {
                        if( cond != mpSubstitutionResults->at( subResComb->first ).at( subResComb->second ).first.begin() )
                            _out << " and ";
                        _out << (**cond).constraint();
                    }
                    _out << "  )" << std::endl;
                }
            }
        }
    }
    
    void State::printSubstitutionResultCombinationAsNumbers( const std::string _initiation, std::ostream& _out ) const
    {
        if( hasSubstitutionResults() )
        {
            if( mpSubResultCombination != NULL )
            {
                _out << _initiation << "Substitution result combination:    ";
                for( auto subResComb = mpSubResultCombination->begin(); subResComb != mpSubResultCombination->end(); ++subResComb )
                    _out << "(" << subResComb->first << ", " << subResComb->second << ")  ";
                _out << std::endl;
            }
        }
    }

    void State::printConflictSets( const std::string _initiation, std::ostream& _out ) const
    {
        _out << _initiation << "Conflict sets: " << std::endl;
        for( auto conflictSet = conflictSets().begin(); conflictSet != conflictSets().end(); ++conflictSet )
        {
            if( conflictSet->first != NULL )
                conflictSet->first->print( true, true, _out, _initiation + "    " );
            else
                _out << _initiation << "    NULL" << std::endl;
            for( auto condSetSet = conflictSet->second.begin(); condSetSet != conflictSet->second.end(); ++condSetSet )
            {
                auto condSet = condSetSet->begin();
                if( condSet != condSetSet->end() )
                {
                    _out << _initiation << "       {";
                    auto cond = (*condSet).begin();
                    if( cond != (*condSet).end() )
                    {
                        _out << " { [";
                        _out << (**cond).constraint();
                        _out << "]" << "_" << (**cond).valuation();
                        ++cond;
                        while( cond != (*condSet).end() )
                        {
                            _out << ", [";
                            _out << (**cond).constraint();
                            _out << "]" << "_" << (**cond).valuation();
                            ++cond;
                        }
                        _out << " }";
                    }
                    else
                        _out << " {}";
                    ++condSet;
                    while( condSet != condSetSet->end() )
                    {
                        _out << "," << std::endl;
                        _out << _initiation << "        ";
                        auto cond = (*condSet).begin();
                        if( cond != (*condSet).end() )
                        {
                            _out << " { [";
                            _out << (**cond).constraint();
                            _out << "]" << "_" << (**cond).valuation();
                            ++cond;
                            while( cond != (*condSet).end() )
                            {
                                _out << ", [";
                                _out << (**cond).constraint();
                                _out << "]" << "_" << (**cond).valuation();
                                ++cond;
                            }
                            _out << " }";
                        }
                        else
                            _out << " {}";
                        ++condSet;
                    }
                    _out << " }" << std::endl;
                }
                else
                    _out << _initiation << "       {}" << std::endl;
            }
        }
    }
    
    #endif

    size_t State::coveringSet( const ConditionSetSetSet& _conflictSets, carl::PointerSet<Condition>& _coveringSet, unsigned _currentTreeDepth )
    {
        // Greatest tree depth of the original conditions of the conditions in the covering set.
        size_t greatestTreeDepth = 0;
        for( auto conflictSet = _conflictSets.begin(); conflictSet != _conflictSets.end(); ++conflictSet )
        {
            if( !conflictSet->empty() )
            {
                // Greatest tree depth of the original conditions of the conditions in the currently best set of conditions in this conflict set.
                size_t greatestTreeDepthConflictSet = 0;
                // The number of conditions in the currently best set of conditions, which are not covered of the so far created covering set.
                size_t numUncovCondsConflictSet = 0;
                auto bestConditionSet = conflictSet->begin();
                for( auto conditionSet = conflictSet->begin(); conditionSet != conflictSet->end(); ++conditionSet )
                {
                    size_t numUncovCondsCondSet = 0;
                    size_t greatestTreeDepthCondSet = 0;
                    bool justEmptyOConds = true;
                    for( auto condition = conditionSet->begin(); condition != conditionSet->end(); ++condition )
                    {
                        if( _coveringSet.find( *condition ) == _coveringSet.end() )
                            numUncovCondsCondSet++;
                        assert( *condition != NULL );
                        for( auto oCond = (**condition).originalConditions().begin(); oCond != (**condition).originalConditions().end(); ++oCond )
                        {
                            assert( *oCond != NULL );
                            justEmptyOConds = false;
                            if( (**oCond).valuation() > greatestTreeDepthCondSet )
                                greatestTreeDepthCondSet = (**oCond).valuation();
                        }
                    }
                    if( justEmptyOConds )
                        greatestTreeDepthCondSet = _currentTreeDepth - 1;
                    if( conditionSet == conflictSet->begin() || (greatestTreeDepthCondSet < greatestTreeDepthConflictSet)
                            || ((greatestTreeDepthCondSet == greatestTreeDepthConflictSet && numUncovCondsCondSet < numUncovCondsConflictSet)) )
                    {
                        bestConditionSet = conditionSet;
                        greatestTreeDepthConflictSet = greatestTreeDepthCondSet;
                        numUncovCondsConflictSet = numUncovCondsCondSet;
                    }
                }
                if( greatestTreeDepthConflictSet > greatestTreeDepth )
                    greatestTreeDepth = greatestTreeDepthConflictSet;
                _coveringSet.insert( bestConditionSet->begin(), bestConditionSet->end() );
            }
        }
        return greatestTreeDepth;
    }
}    // end namspace vs
}