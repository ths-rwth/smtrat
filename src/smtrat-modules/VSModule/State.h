/**
 * Class to create a decision tuple object.
 * @author Florian Corzilius
 * @since 2010-05-11
 * @version 2013-10-24
 */

#pragma once

#include <map>
#include <limits.h>
#include "Substitution.h"
#include <carl-common/memory/IDPool.h>
#include <smtrat-variablebounds/VariableBounds.h>
#include "VSSettings.h"

#ifdef SMTRAT_DEVOPTION_Statistics
#include "VSStatistics.h"
#endif

#define VS_STATE_DEBUG_METHODS

namespace smtrat {
namespace vs
{
    
    // Type and object definitions.
    typedef std::set< carl::PointerSet<Condition> > ConditionSetSet;
    typedef std::set< ConditionSetSet > ConditionSetSetSet;
    typedef std::list< const Condition* > ConditionList;
    typedef std::vector< ConditionList >  DisjunctionOfConditionConjunctions;
    
    typedef std::pair<size_t, std::pair<size_t, size_t> > UnsignedTriple;

    // Forward declaration.
    class State;
    
    struct unsignedTripleCmp
    {
        bool operator ()( UnsignedTriple n1, UnsignedTriple n2 ) const
        {
            if( n1.first > n2.first )
                return true;
            else if( n1.first == n2.first )
            {
                if( n1.first != 1 )
                    return n1.second.first > n2.second.first;
                else
                {
                    if( n1.second.second < n2.second.second )
                        return true;
                    else if( n1.second.second == n2.second.second )
                        return n1.second.first > n2.second.first;
                    return false;
                }
            }
            else
                return false;
        }
    };
    typedef std::pair<UnsignedTriple, vs::State*> ValStatePair;
    typedef std::map<UnsignedTriple, vs::State*, unsignedTripleCmp> ValuationMap;

    class State
    {
    public:
        // Internal type definitions.
        enum Type{ TEST_CANDIDATE_TO_GENERATE, SUBSTITUTION_TO_APPLY, COMBINE_SUBRESULTS };
        
        typedef carl::FastPointerMapB<Substitution,ConditionSetSetSet> ConflictSets;
        typedef std::vector<std::pair< ConditionList, bool>> SubstitutionResult;
        typedef std::vector<SubstitutionResult> SubstitutionResults;   
        typedef std::vector<std::pair< unsigned, unsigned>> SubResultCombination;
        typedef smtrat::vb::VariableBounds<const Condition*> VariableBoundsCond;
    private:
        
        // Members:

        /// A flag indicating whether the conditions this state considers are simplified.
        bool mConditionsSimplified;
        /// A flag indicating whether there are states that are children of this state and must 
        /// be still considered in the further progress of finding a solution.
        bool mHasChildrenToInsert;
        /// A flag that indicates whether this state has conditions in its considered list of
        /// conditions, which were recently added and, hence, must be propagated further.
        bool mHasRecentlyAddedConditions;
        /// A flag that indicates whether this state is already inconsistent. Note that if it 
        /// is set to false, it does not necessarily mean that this state is consistent.
        bool mInconsistent;
        /// A flag indicating whether this state has already marked as deleted, which means
        /// that there is no need to consider it in the further progress of finding a solution.
        bool mMarkedAsDeleted;
        /// A flag indicating whether the substitution results this state are simplified.
        bool mSubResultsSimplified;
        /// A flag indicating whether to take the current combination of substitution results
        /// once again.
        bool mTakeSubResultCombAgain;
        /// A flag indicating whether the test candidate contained by this state has already been
        /// check for the bounds of the variables.
        bool mTestCandidateCheckedForBounds;
        /// A flag indicating whether this state has been progressed until a point where a condition
        /// must be involved having a too high degree to tackle with virtual substitution. Note, that
        /// this flag is also set to true if heuristics decide that the combinatorial blow up using
        /// virtual substitution for the considered list of conditions of this state is too high.
        /// If this flag is set to true, it the state is delayed until a point where only such state
        /// remain and a backend must be involved.
        bool mCannotBeSolved;
        /// 
        bool mCannotBeSolvedLazy;
        /// A flag indicating whether the index (the variable to eliminate in this state) should be
        /// reconsidered and maybe changed.
        bool mTryToRefreshIndex;
        /// A heuristically determined value stating the expected difficulty of this state's considered
        /// conditions to be solved by a backend. The higher this value, the easier it should be to
        /// solve this state's considered conditions.
        size_t mBackendCallValuation;
        /// A unique id identifying this state.
        size_t mID;
        /// A heuristically determined value stating the expected difficulty of this state's considered
        /// conditions to be solved by virtual substitution. The higher this value, the easier it should be to
        /// solve this state's considered conditions. Furthermore, this value enforces currently a depth first
        /// search, as a child has always a higher valuation than its father.
        size_t mValuation;
        /// The type of this state, which states whether this state has still a substitution to apply or either
        /// test candidates shall be generated or a new combination of the substitution results must be found
        /// in order to consider it next.
        Type mType;
        /// The variable which is going to be eliminated from this state's considered conditions. That means, 
        /// this variable won't occur in the children of this state.
        carl::Variable mIndex;
        /// If the test candidate considered by this state stems from a condition for which it is enough to
        /// consider it only for test candidate generation for finding the satisfiability of the conditions
        /// it occurs in, this member stores that condition. It is necessary, as it must be part of the origins
        /// (conditions in the father of this state) of any conflict found in this state.
        const Condition* mpOriginalCondition;
        /// The father state of this state.
        State* mpFather;
        /// The substitution this state considers. Note that it is NULL if this state is the root.
        Substitution* mpSubstitution;
        /// The vector storing the substitution results, that is for each application of the substitution in
        /// this state to one of its considered conditions a disjunction of conjunctions of constraints.
        SubstitutionResults* mpSubstitutionResults;
        /// The currently considered combination of conjunctions of constraints in the substitution
        /// result vector, which form the currently considered conditions of this state (store in mpConditions).
        SubResultCombination* mpSubResultCombination;
        /// The currently considered conditions of this state, for which the satisfiability must be checked.
        ConditionList* mpConditions;
        /// Stores for each already considered and failed test candidate all conflicts which have been found for it.
        ConflictSets* mpConflictSets;
        /// The children states of this state. For each test candidate we generate for the conditions this state 
        /// considers such a child is created.
        std::list< State* >* mpChildren;
        /// The conditions of this state, which cannot be solved by the virtual substitution.
        carl::PointerSet<Condition>* mpTooHighDegreeConditions;
        /// A pointer to an object which manages and stores the bounds on the variables occurring in this state.
        /// These bounds are filtered from the conditions this state considers. Note that if we do not use 
        /// optimizations based on variable bounds.
        VariableBoundsCond* mpVariableBounds;
        ///
        State* mpInfinityChild;
        ///
        smtrat::Rational mMinIntTestCanidate;
        ///
        smtrat::Rational mMaxIntTestCanidate;
        ///
        size_t mCurrentIntRange;
        ///
        carl::IDPool* mpConditionIdAllocator;
        ///
        std::vector<std::pair<carl::Variable,std::multiset<double>>> mRealVarVals;
        ///
        std::vector<std::pair<carl::Variable,std::multiset<double>>> mIntVarVals;
        ///
        std::vector<size_t> mBestVarVals;
            
        #ifdef SMTRAT_DEVOPTION_Statistics
        /// Stores all collected statistics during solving.
        smtrat::VSStatistics* mpStatistics;
        #endif
        
    public:
        
        /**
         * Constructs an empty state (no conditions yet) being the root (hence neither a substitution) of the state 
         * tree which is going to be formed when applying the satisfiability check based on virtual substitution.
         * @param _withVariableBounds A flag that indicates whether to use optimizations based on variable bounds.
         */
        State( carl::IDPool* _conditionIdAllocator, bool _withVariableBounds );
        
        /**
         * Constructs a state being a child of the given state and containing the given substitution, which maps
         * from the index variable of the given state.
         * @param _father The father of the state to be constructed.
         * @param _substitution The substitution of the state to be constructed.
         * @param _withVariableBounds A flag that indicates whether to use optimizations based on variable bounds.
         */
        State( State* const _father, const Substitution& _substitution, carl::IDPool* _conditionIdAllocator, bool _withVariableBounds );
        
        State( const State& ) = delete;

        /**
         * Destructor.
         */
        ~State();

        /**
         * @return The root of the state tree where this state is part from.
         */
        bool isRoot() const
        {
            return mpFather == NULL;
        }

        /**
         * @return A constant reference to the flag indicating whether a condition with too high degree for 
         *          the virtual substitution method must be considered.
         */
        bool cannotBeSolved( bool _lazy ) const
        {
            return mCannotBeSolved || (_lazy && mCannotBeSolvedLazy);
        }
        
        /**
         * @return A reference to the flag indicating whether a condition with too high degree for 
         *          the virtual substitution method must be considered.
         */
        bool& rCannotBeSolved()
        {
            return mCannotBeSolved;
        }
        
        /**
         * @return A reference to the flag indicating whether a condition with too high degree for 
         *          the virtual substitution method must be considered.
         */
        bool& rCannotBeSolvedLazy()
        {
            return mCannotBeSolvedLazy;
        }

        /**
         * @return A constant reference to the flag indicating whether this state is marked as deleted, which
         *          means that there is no need to consider it in the further progress of finding a solution.
         */
        bool markedAsDeleted() const
        {
            return mMarkedAsDeleted;
        }

        /**
         * @return A reference to the flag indicating whether this state is marked as deleted, which
         *          means that there is no need to consider it in the further progress of finding a solution.
         */
        bool& rMarkedAsDeleted()
        {
            return mMarkedAsDeleted;
        }

        /**
         * @return A constant reference to the flag indicating whether there are states that are children 
         *          of this state and must be still considered in the further progress of finding a solution.
         */
        bool hasChildrenToInsert() const
        {
            return mHasChildrenToInsert;
        }

        /**
         * @return A reference to the flag indicating whether there are states that are children 
         *          of this state and must be still considered in the further progress of finding a solution.
         */
        bool& rHasChildrenToInsert()
        {
            return mHasChildrenToInsert;
        }

        /**
         * @return A constant reference to the variable which is going to be eliminated from this state's 
         *          considered conditions. Note, if there is no variable decided to be eliminated, this
         *          method will fail.
         */
        carl::Variable::Arg index() const
        {
            return mIndex;
        }

        /**
         * @return The heuristically determined valuation of this state (see for the description of the
         *          corresponding member).
         */
        size_t valuation() const
        {
            return mValuation;
        }
        
        /**
         * @return The valuation of the state's considered conditions for a possible backend call.
         */
        size_t backendCallValuation() const
        {
            return mBackendCallValuation;
        }

        /**
         * @return The id of this state.
         */
        size_t id() const
        {
            return mID;
        }
        
        /**
         * @return A reference to the id of this state.
         */
        size_t& rID()
        {
            return mID;
        }

        /**
         * @return A reference to the vector of the children of this state.
         */
        std::list<State*>& rChildren()
        {
            return *mpChildren;
        }

        /**
         * @return A constant reference to the vector of the children of this state.
         */
        const std::list<State*>& children() const
        {
            return *mpChildren;
        }

        /**
         * @return A pointer to the father of this state. It is NULL if this state is the root.
         */
        State* pFather() const
        {
            return mpFather;
        }

        /**
         * @return A constant reference to the father of this state. This method fails if this state is the root.
         */
        const State& father() const
        {
            return *mpFather;
        }

        /**
         * @return A reference to the father of this state. This method fails if this state is the root.
         */
        State& rFather()
        {
            return *mpFather;
        }

        /**
         * @return A reference to the conflict sets of this state.
         */
        ConflictSets& rConflictSets()
        {
            return *mpConflictSets;
        }
        
        /**
         * @return A constant reference to the conflict sets of this state.
         */
        const ConflictSets&	conflictSets() const
        {
            return *mpConflictSets;
        }

        /**
         * @return A reference to the flag indicating that this state has a recently added condition in 
         *          its considered conditions.
         */
        bool& rHasRecentlyAddedConditions()
        {
            return mHasRecentlyAddedConditions;
        }

        /**
         * @return true, if this state has a recently added condition in its considered conditions.
         */
        bool hasRecentlyAddedConditions() const
        {
            return mHasRecentlyAddedConditions;
        }

        /**
         * @return A reference to the flag indicating whether this state's considered conditions are inconsistent.
         *          Note that if it is false, it does not necessarily mean that this state is consistent.
         */
        bool& rInconsistent()
        {
            return mInconsistent;
        }

        /**
         * @return true if this state's considered conditions are inconsistent;
         *          false, otherwise, which does not necessarily mean that this state is consistent.
         */
        bool isInconsistent() const
        {
            return mInconsistent;
        }

        /**
         * @return A reference to the currently considered conditions of this state.
         */
        ConditionList& rConditions()
        {
            return *mpConditions;
        }

        /**
         * @return A constant reference to the currently considered conditions of this state.
         */
        const ConditionList& conditions() const
        {
            return *mpConditions;
        }

        /**
         * @return A reference to the substitution this state considers. Note that this method fails,
         *          if this state is the root.
         */
        Substitution& rSubstitution()
        {
            return *mpSubstitution;
        }

        /**
         * @return A constant reference to the substitution this state considers. Note that this method fails,
         *          if this state is the root.
         */
        const Substitution&	substitution() const
        {
            return *mpSubstitution;
        }

        /**
         * @return A reference to the substitution results of this state. Make sure that the substitution
         *          results exist when calling this method. (using, e.g., hasSubstitutionResults())
         */
        SubstitutionResults& rSubstitutionResults()
        {
            return *mpSubstitutionResults;
        }
        
        /**
         * @return A constant reference to the substitution results of this state. Make sure that the substitution
         *          results exist when calling this method. (using, e.g., hasSubstitutionResults())
         */
        const SubstitutionResults& substitutionResults() const
        {
            return *mpSubstitutionResults;
        }
        
        /**
         * @return A reference to the current combination of conjunction of constraints within the substitution 
         *          results of this state. Make sure that a substitution result combination exists when calling 
         *          this method. (using, e.g., hasSubResultsCombination())
         */
        SubResultCombination& rSubResultCombination()
        {
            return *mpSubResultCombination;
        }
        
        /**
         * @return A constant reference to the current combination of conjunction of constraints within the substitution 
         *          results of this state. Make sure that a substitution result combination exists when calling 
         *          this method. (using, e.g., hasSubResultsCombination())
         */
        const SubResultCombination&	subResultCombination() const
        {
            return *mpSubResultCombination;
        }

        /**
         * @return A pointer to the substitution of this state, which is NULL, if this state is the root.
         */
        const Substitution* pSubstitution() const
        {
            return mpSubstitution;
        }

        /**
         * @return true, if the considered conditions of this state are already simplified.
         */
        bool conditionsSimplified() const
        {
            return mConditionsSimplified;
        }
        
       /**
        * @return true, if the substitution results of this state are already simplified.
        */
        bool subResultsSimplified() const
        {
            return mSubResultsSimplified;
        }

        /**
         * @return A reference to the flag indicating whether the substitution results of this state are already simplified.
         */
        bool& rSubResultsSimplified()
        {
            return mSubResultsSimplified;
        }

        /**
         * @return true, if the current substitution result combination has to be consider once again before considering 
         *                the next one.
         */
        bool takeSubResultCombAgain() const
        {
            return mTakeSubResultCombAgain;
        }
        
        /**
         * @return A reference to the flag indicating whether the current substitution result combination has to be consider 
         *          once again before considering the next one.
         */
        bool& rTakeSubResultCombAgain()
        {
            return mTakeSubResultCombAgain;
        }

        /**
         * @return true, if the index variable of this state shall be recalculated.
         */
        bool tryToRefreshIndex() const
        {
            return mTryToRefreshIndex;
        }

        /**
         * @return true, if this state has a substitution result combination.
         */
        bool hasSubResultsCombination() const
        {
            return (mpSubResultCombination!=NULL && !mpSubResultCombination->empty());
        }

        /**
         * @return true, if this state has substitution results.
         */
        bool hasSubstitutionResults() const
        {
            return mpSubstitutionResults!=NULL;
        }

        /**
         * @return true, if the currently considered substitution result combination can be extended by
         *                taking further substitution results into account.
         */
        bool unfinished() const
        {
            return (mpSubstitutionResults->size()>mpSubResultCombination->size());
        }

        /**
         * @return The type of this state: This state has still a substitution to apply or either
         * test candidates shall be generated or a new combination of the substitution results must be found
         * in order to consider it next.
         */
        Type type() const
        {
            return mType;
        }
        
        /**
         * @return A constant reference to the type of this state: This state has still a substitution to 
         * apply or either test candidates shall be generated or a new combination of the substitution 
         * results must be found in order to consider it next.
         */
        Type& rType()
        {
            return mType;
        }

        /**
         * @return A pointer to the original condition of this state or NULL, if there is no such condition.
         *          For further information see the description of the corresponding member.
         */
        const Condition* pOriginalCondition() const
        {
            return mpOriginalCondition;
        }

        /**
         * @return A reference to the original conditions of this state. Note that if there is no such condition,
         *          this method fails. For further information see the description of the corresponding member.
         */
        const Condition& originalCondition() const
        {
            return *mpOriginalCondition;
        }
        
        /**
         * @return A constant reference to the conditions of those this state currently considers, which have a 
         *          too high degree to be tackled of the virtual substitution method.
         */
        const carl::PointerSet<Condition>& tooHighDegreeConditions() const
        {
            return *mpTooHighDegreeConditions;
        }
        
        /**
         * @return A reference to the conditions of those this state currently considers, which have a 
         *          too high degree to be tackled of the virtual substitution method.
         */
        carl::PointerSet<Condition>& rTooHighDegreeConditions()
        {
            return *mpTooHighDegreeConditions;
        }

        /**
         * @return A constant reference to the object managing and storing the variable's bounds which were
         *          extracted from the currently considered conditions of this state.
         */
        const VariableBoundsCond& variableBounds() const
        {
            assert( mpVariableBounds != NULL );
            return *mpVariableBounds;
        }

        /**
         * @return A reference to the object managing and storing the variable's bounds which were
         *          extracted from the currently considered conditions of this state.
         */
        VariableBoundsCond& rVariableBounds()
        {
            assert( mpVariableBounds != NULL );
            return *mpVariableBounds;
        }

        /**
         * Sets the pointer of the original condition of this state to the given pointer to a condition.
         * @param _pOCondition The pointer to set the original condition to.
         */
        void setOriginalCondition( const Condition* _pOCondition )
        {
            mpOriginalCondition = _pOCondition;
        }
        
        /**
         *
         */
        size_t currentRangeSize() const
        {
            return mCurrentIntRange;
        }
        
        /**
         *
         */
        void resetCurrentRangeSize()
        {
            assert( !isRoot() || substitution().type() == Substitution::MINUS_INFINITY || substitution().type() == Substitution::PLUS_INFINITY );
            mCurrentIntRange = 0;
            mCannotBeSolved = !mpTooHighDegreeConditions->empty();
        }
        
        /**
         * 
         */
        const smtrat::Rational& minIntTestCandidate() const
        {
            return mMinIntTestCanidate;
        }
        
        /**
         * .
         */
        const smtrat::Rational& maxIntTestCandidate() const
        {
            return mMaxIntTestCanidate;
        }
        
        bool hasInfinityChild() const
        {
            return mpInfinityChild != NULL;
        }
        
        void resetInfinityChild( const State* _state )
        {
            if( mpInfinityChild == _state )
                mpInfinityChild = NULL;
        }
        
        void setInfinityChild( State* _state )
        {
            assert( mpInfinityChild == NULL );
            mpInfinityChild = _state;
        }
        
        #ifdef SMTRAT_DEVOPTION_Statistics
        void setStatistics( smtrat::VSStatistics* _stats )
        {
            assert( mpStatistics == nullptr );
            mpStatistics = _stats;
        }
        
        carl::uint numberOfUnusedConditions() const
        {
            carl::uint result = 0;
            for( const Condition* cond : conditions() )
            {
                if( !cond->flag() )
                    ++result;
            }
            return result;
        }
        #endif
        
        static void removeStatesFromRanking( const State& toRemove, ValuationMap& _ranking );
        
        void resetCannotBeSolvedLazyFlags();

        /**
         * @return The depth of the subtree with this state as root node.
         */
        unsigned treeDepth() const;
        
        /**
         * Checks if a substitution can be applied.
         * @return true, if a substitution can be applied.
         *          false, else.
         */
        bool substitutionApplicable() const;
        
        /**
         * Checks if the substitution of this state can be applied to the given constraint.
         * @param _constraint The constraint, for which we want to know, if the substitution is applicable.
         * @return true, if the substitution can be applied;
         *          false, otherwise.
         */
        bool substitutionApplicable( const smtrat::ConstraintT& _constraint ) const;
        
        /**
         * Checks whether a condition exists, which was not involved in an elimination step.
         * @return true, if there exists a condition in the state, which was not already involved in an elimination step;
         *          false, otherwise.
         */
        bool hasNoninvolvedCondition() const;
        
        /**
         * @param A condition, which is one of the currently considered constraints to check for satisfiability.
         * @return true, if all test candidates provided by the given condition are no solution of the currently considered 
         *          conjunction of constraints to check for satisfiability.
         */
        bool allTestCandidatesInvalidated( const Condition* _condition ) const;
        
        /**
         * Checks whether a child exists, which has no ID (!=0).
         * @return true, if there exists a child with ID (!=0);
         *          false, otherwise.
         */
        bool hasChildWithID() const;
        
        /**
         * @return true, if the given state is a node in the state tree starting at this node;
         *          false, otherwise.
         */
        bool containsState( const State* _state ) const;
            
        /**
         * Checks whether a child exists, which is not yet marked as inconsistent.
         * @return true, if there exists such a child;
         *          false, otherwise.
         */
        bool hasOnlyInconsistentChildren() const;
        
        /**
         * Checks whether the given variable occurs in a equation.
         * @return true,   if the given variable occurs in a equation;
         *          false,  otherwise.
         */
        bool occursInEquation( const carl::Variable& ) const;
        
        /**
         * Checks whether there exist more than one test candidate, which has still not been checked.
         *
         * @return  true, if there exist more than one test candidate, which has still not been checked;
         *          false, otherwise.
         */
        bool hasFurtherUncheckedTestCandidates() const;
        
        /**
         * Finds the variables, which occur in this state.
         * @param _variables The variables which occur in this state.
         */
        void variables( carl::Variables& _variables ) const;
        
        /**
         * Determines the number of nodes in the tree with this state as root.
         * @return The number of nodes in the tree with this state as root.
         */
        unsigned numberOfNodes() const;

        /**
         * @return The root of the tree, in which this state is located.
         */
        State& root();
        
        /**
         */
        bool getNextIntTestCandidate( smtrat::Rational& _nextIntTestCandidate, size_t _maxIntRange );
        
        /**
         * 
         */
        bool updateIntTestCandidates();
        
        /**
         * Determines (if it exists) a ancestor node, which is unfinished, that is
         * it has still substitution results to consider.
         * @param _unfinAnt The unfinished ancestor node.
         * @return true, if it has a unfinished ancestor;
         *          false, otherwise.
         */
        bool unfinishedAncestor( State*& _unfinAnt );
        
        /**
         * Determines the most adequate condition and in it the most adequate variable in
         * the state to generate test candidates for.
         * @param _bestCondition The most adequate condition to be the next test candidate provider.
         * @param _numberOfAllVariables The number of all globally known variables.
         * @param _preferEquation A flag that indicates to prefer equations in the heuristics of this method.
         * @return true, if it has a condition and a variable in it to generate test candidates for;
         *          false, otherwise.
         */
        bool bestCondition( const Condition*& _bestCondition, size_t _numberOfAllVariables, bool _preferEquation );
        
        /**
         * Checks if the given constraint already exists as condition in the state.
         * @param _constraint The constraint, for which we want to know, if it already
         *                     exists as condition in the state.
         * @return An iterator to the condition, which involves the constraint or an iterator
         *          to the end of the vector of conditions of this state.
         */
        ConditionList::iterator	constraintExists( const smtrat::ConstraintT& _constraint );

        /**
         * Cleans up all conditions in this state according to comparison between the corresponding constraints.
         */
        void simplify( ValuationMap& _ranking );
        
        /**
         * Simplifies the given conditions according to comparison between the corresponding constraints.
         * @param _conditionVectorToSimplify The conditions to simplify. Note, that this method can change these conditions.
         * @param _conflictSet All conflicts this method detects in the given conditions are stored in here.
         * @param _stateConditions A flag indicating whether the conditions to simplify are from the considered
         *                          condition vector of this state and not, e.g., from somewhere in its
         *                          substitution results.
         * @return true, if the conditions are not obviously conflicting;
         *          false, otherwise.
         */
        bool simplify( ConditionList& _conditionVectorToSimplify, ConditionSetSet& _conflictSet, ValuationMap& _ranking, bool _stateConditions = false );
        
        /**
         * Sets the index of this state.
         * @param _index The string to which the index should be set.
         */
        void setIndex( const carl::Variable& _index );
        
        /**
         * Adds a conflict set to the map of substitutions to conflict sets.
         * @param _substitution The corresponding substitution generated the conflict.
         *                      (NULL in the case a detected conflict without substitution)
         * @param _condSetSet The conflicts to add.
         */
        void addConflictSet( const Substitution* _substitution, ConditionSetSet&& _condSetSet );
        
        /**
         * Adds all conflicts to all sets of the conflict set of the given substitution.
         * @param _substitution The corresponding substitution generated the conflict.
         *                      (NULL in the case a detected conflict without substitution)
         * @param _condSetSet The conflicts to add.
         */
        void addConflicts( const Substitution* _substitution, ConditionSetSet&& _condSetSet );
        
        /**
         * Clears the conflict sets.
         */
        void resetConflictSets();
        
        /**
         * Updates the original conditions of substitutions having the same test candidate as the given.
         * @param _substitution The substitution containing the test candidate to check for.
         * @param _reactivatedStates
         * @return true, if the test candidate of the given substitution was already generated;
         *          false, otherwise.
         */
        bool updateOCondsOfSubstitutions( const Substitution& _substitution, std::vector<State*>& _reactivatedStates );
        
        /**
         * Adds the given substitution results to this state.
         * @param _disjunctionsOfCondConj The substitution results given by a vector
         *                                 of disjunctions of conjunctions of conditions.
         */
        void addSubstitutionResults( std::vector< DisjunctionOfConditionConjunctions >&& _disjunctionsOfCondConj );
        
        /**
         * Extends the currently considered combination of conjunctions in the substitution results.
         */
        bool extendSubResultCombination();
        
        /**
         * If the state contains a substitution result, which is a conjunction of disjunctions of
         * conjunctions of conditions, this method sets the current combination to the disjunctions
         * to the next combination.
         * @return true, if there is a next combination;
         *          false, otherwise.
         */
        bool nextSubResultCombination();
        
        /**
         * @return The number of the current substitution result combination.
         */
        size_t getNumberOfCurrentSubresultCombination() const;
        
        /**
         * Gets the current substitution result combination as condition vector.
         * @return The current substitution result combination as condition vector.
         */
        ConditionList getCurrentSubresultCombination() const;
        
        /**
         * Determines the condition vector corresponding to the current combination of the
         * conjunctions of conditions.
         * @return true, if there has been a change in the currently considered condition vector.
         *          false, otherwise.
         */
        bool refreshConditions( ValuationMap& _ranking );
         
        /**
         * Sets all flags of the conditions to true, if it contains the variable given by the states index.
         */
        void initConditionFlags();
        
        /**
         * Sets, if it has not already happened, the index of the state to the name of the
         * most adequate variable. Which variable is taken depends on heuristics.
         * @param _allVariables All globally known variables.
         * @param _vvstrat The strategy according which we choose the variable.
         * @param _preferEquation A flag that indicates to prefer equations in the heuristics of this method.
         * @param _tryDifferentVarOrder
         */
        bool initIndex( const carl::Variables& _allVariables, const smtrat::VariableValuationStrategy& _vvstrat, bool _preferEquation, bool _tryDifferentVarOrder = false, bool _useFixedVariableOrder = false );
        void bestConstraintValuation( const std::vector<std::pair<carl::Variable, std::multiset<double>>>& _varVals );
        void averageConstraintValuation( const std::vector<std::pair<carl::Variable, std::multiset<double>>>& _varVals );
        void worstConstraintValuation( const std::vector<std::pair<carl::Variable, std::multiset<double>>>& _varVals );
        
        /**
         * Adds a constraint to the conditions of this state.
         * @param _constraint The constraint of the condition to add.
         * @param _originalConditions The original conditions of the condition to add.
         * @param _valutation The valuation of the condition to add.
         * @param _recentlyAdded Is the condition a recently added one.
         * @sideeffect The state can obtain a new condition.
         */
        void addCondition( const smtrat::ConstraintT& _constraint, const carl::PointerSet<Condition>& _originalConditions, size_t _valutation, bool _recentlyAdded, ValuationMap& _ranking );
        
        /**
         * This is just for debug purpose.
         * @return true, if no subresult combination is illegal.
         */
        bool checkSubresultCombinations() const;
            
        /**
         * Removes everything in this state originated by the given vector of conditions.
         * @param _originsToDelete The conditions for which everything in this state which
         *                          has been originated by them must be removed.
         * @return 0, if this state got invalid and must be deleted afterwards;
         *          -1, if this state got invalid and must be deleted afterwards
         *              and made other states unnecessary to consider;
         *          1, otherwise.
         */
        int deleteOrigins( carl::PointerSet<Condition>& _originsToDelete, ValuationMap& _ranking );
            
        /**
         * Deletes everything originated by the given conditions in the children of this state.
         * @param _originsToDelete The condition for which to delete everything originated by them.
         */
        void deleteOriginsFromChildren( carl::PointerSet<Condition>& _originsToDelete, ValuationMap& _ranking );
            
        /**
         * Deletes everything originated by the given conditions in the conflict sets of this state.
         * @param _originsToDelete The condition for which to delete everything originated by them.
         * @param _originsAreCurrentConditions A flag indicating whether the origins to remove stem from
         *                          conditions of the currently considered condition vector of the father 
         *                          of this state and not, e.g., from somewhere in its substitution results.
         */
        void deleteOriginsFromConflictSets( carl::PointerSet<Condition>& _originsToDelete, bool _originsAreCurrentConditions );
            
        /**
         * Deletes everything originated by the given conditions in the substitution results of this state.
         * @param _originsToDelete The conditions for which to delete everything originated by them.
         */
        void deleteOriginsFromSubstitutionResults( carl::PointerSet<Condition>& _originsToDelete );
        
        /**
         * Delete everything originated by the given conditions from the entire subtree with this state as root.
         * @param _conditionsToDelete The conditions to delete.
         */
        void deleteConditions( carl::PointerSet<Condition>& _conditionsToDelete, ValuationMap& _ranking );
        
        /**
         * Adds a state as child to this state with the given substitution.
         * @param _substitution The substitution to generate the state for.
         * @return true, if a state has been added as child to this state;
         *          false, otherwise.
         */
        std::vector<State*> addChild( const Substitution& _substitution );
        
        /**
         * Updates the valuation of this state.
         */
        void updateValuation( bool _lazy );
        
        /**
         * Valuates the state's currently considered conditions according to a backend call.
         * Note: The settings are currently optimized for CAD backend calls.
         */
        void updateBackendCallValuation();
            
        /**
         * Passes the original conditions of the covering set of the conflicts of this state to its father.
         * @param _checkConflictForSideCondition If this flag is set to false it might save some computations
         *                                        but leads to an over-approximative behavior. Recommendation: set it to true.
         * @param _includeInconsistentTestCandidates If this flag is set to true the conflict analysis takes also the
         *                                            invalid test candidates' conflict sets into account. Recommendation: set 
         *                                            it to false.
         * @param _useBackjumping If true, we use the backjumping technique.
         */
        void passConflictToFather( bool _checkConflictForSideCondition, bool _useBackjumping = true, bool _includeInconsistentTestCandidates = false );
           
        /**
         * Checks whether the currently considered conditions, which have been considered for test candidate 
         * construction, form already a conflict.
         * @return true, if they form a conflict;
         *          false, otherwise.
         */
        bool hasLocalConflict();
        
        /**
         * Checks whether the test candidate of this state is valid against the variable intervals
         * in the father of this state.
         * @return true, if the test candidate of this state is valid against the variable intervals;
         *          false, otherwise.
         */
        bool checkTestCandidatesForBounds();
            
        /**
         * Determines the solution space of the test candidate of this state regarding to
         * the variable bounds of the father. The solution space consists of one or two
         * disjoint intervals.
         * @param _conflictReason If the solution space is empty, the conditions being
         *                         responsible for this conflict are stored in here.
         * @return The disjoint intervals representing the solution space.
         */
        std::vector< smtrat::DoubleInterval > solutionSpace( carl::PointerSet<Condition>& _conflictReason ) const;
        
        /**
         * Checks whether there are no zeros for the left-hand side of the constraint of the given condition.
         * @param _condition The condition to check.
         * @param A flag that indicates whether to include Sturm's sequences and root counting in this method.
         * @return true, if the constraint of the left-hand side of the given condition has no roots 
         *                in the variable bounds of this state;
         *          false, otherwise.
         */
        bool hasRootsInVariableBounds( const Condition* _condition, bool _useSturmSequence );
        
        #ifdef VS_STATE_DEBUG_METHODS

        /**
         * Prints the conditions, the substitution and the substitution results of this state and 
         * all its children.
         * @param _initiation A string which is printed in the beginning of every row.
         * @param _out The stream to print on.
         */
        void print( const std::string _initiation = "***", std::ostream& _out = std::cout ) const;
        
        /**
         * Prints the conditions, the substitution and the substitution results of this state.
         * @param _initiation A string which is printed in the beginning of every row.
         * @param _out The stream to print on.
         */
        void printAlone( const std::string = "***", std::ostream& _out = std::cout ) const;
        
        /**
         * Prints the conditions of this state.
         * @param _initiation A string which is printed in the beginning of every row.
         * @param _out The stream to print on.
         */
        void printConditions( const std::string _initiation = "***", std::ostream& _out = std::cout, bool = false ) const;
        
        /**
         * Prints the substitution results of this state.
         * @param _initiation A string which is printed in the beginning of every row.
         * @param _out The stream to print on.
         */
        void printSubstitutionResults( const std::string _initiation = "***", std::ostream& _out = std::cout	) const;
        
        /**
         * Prints the combination of substitution results used in this state.
         * @param _initiation A string which is printed in the beginning of every row.
         * @param _out The stream to print on.
         */
        void printSubstitutionResultCombination( const std::string _initiation = "***", std::ostream& _out = std::cout	) const;
        
        /**
         * Prints the combination of substitution results, expressed in numbers, used in this state.
         * @param _initiation A string which is printed in the beginning of every row.
         * @param _out The stream to print on.
         */
        void printSubstitutionResultCombinationAsNumbers( const std::string _initiation = "***", std::ostream& _out = std::cout ) const;
        
        /**
         * Prints the conflict sets of this state.
         * @param _initiation A string which is printed in the beginning of every row.
         * @param _out The stream to print on.
         */
        void printConflictSets( const std::string _initiation = "***", std::ostream& _out = std::cout ) const;
        
        #endif

        /**
         * Finds a covering set of a vector of sets of sets due to some heuristics.
         * @param _conflictSets The vector of sets of sets, for which the method finds all minimum covering sets.
         * @param _minCovSet The found mininum covering set.
         * @param _currentTreeDepth The tree depth of the state from which this method is invoked.
         * @return The greatest level, where a condition of the covering set has been created.
         */
        static size_t coveringSet( const ConditionSetSetSet& _conflictSets, carl::PointerSet<Condition>& _minCovSet, unsigned _currentTreeDepth );
    };
} // end namspace vs
}