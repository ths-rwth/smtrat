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
 * @file VSModule.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * Created on January 18, 2012, 3:45 PM
 */

#pragma once

//#define VS_STATISTICS
//#define VS_PRINT_ANSWERS
//#define VS_LOG_INTERMEDIATE_STEPS

#include "../../Common.h"
#include "Substitute.h"
#include "State.h"
#include "VSSettings.h"
#include "IDAllocator.h"
#include "../../solver/Module.h"
#include "../../solver/RuntimeSettings.h"

namespace smtrat
{
    template<class Settings>
    class VSModule: public Module
    {
        private:

            /// A map from constraints represented by carl::formulas to vs::conditions.
            typedef std::map<FormulaT, const vs::Condition*> FormulaConditionMap;
            /// A vector of carl::variable pairs.
            typedef std::vector<std::pair<carl::Variable,carl::Variable>> VarPairVector;

            // Members.
            
            /// A flag being true, if a condition in the root state has been changed after the last consistency check.
            bool mConditionsChanged;
            /// A flag being true, if it is known that a constraint has been added to the root state, which is inconsistent itself.
            bool mInconsistentConstraintAdded;
            /// For the allocation of unique ids for the states.
            size_t mIDCounter;
            #ifdef VS_STATISTICS
            /// 
            size_t mStepCounter;
            #endif
            /// Id allocator for the conditions.
            vs::IDAllocator* mpConditionIdAllocator;
            ///
            vs::State* mpStateTree;
            ///
            carl::Variables mAllVariables;
            ///
            FormulaConditionMap mFormulaConditionMap;
            /// The order for all states, in which they shall be processed. The first state in this map is processed first.
            vs::ValuationMap mRanking;
            /**
             * Stores for each depth in the state tree (hence, for the variable eliminated in that state) a 
             * variable for minus infinity (the first) and epsilon (the second).
             */
            mutable VarPairVector mVariableVector;

        public:

            // Constructors.
            VSModule( ModuleType _type, const ModuleInput*, RuntimeSettings*, Conditionals&, Manager* const = NULL );

            // Destructor.
            ~VSModule();
            
            // Interfaces.
            bool assertSubformula( ModuleInput::const_iterator );
            Answer isConsistent();
            void removeSubformula( ModuleInput::const_iterator );
            void updateModel() const;

        private:

            /// A pair of a substitution and the states which belong to this substitution.
            typedef std::pair<vs::Substitution, std::list< vs::State* >> ChildrenGroup;
            /// A vector of pairs of a substitution and the states which belong to this substitution.
            typedef std::vector<ChildrenGroup> ChildrenGroups;

            /**
             * Increase the counter for id allocation.
             */
            void increaseIDCounter()
            {
                assert( mIDCounter < UINT_MAX );
                mIDCounter++;
            }
            
            /**
             * @return 
             */
            inline Answer consistencyTrue();
            
            /**
             * Eliminates the given variable by finding test candidates of the constraint of the given
             * condition. All this happens in the state _currentState.
             * @param _currentState   The currently considered state.
             * @param _eliminationVar The substitution to apply.
             * @param _condition      The condition with the constraint, in which should be substituted.
             * @sideeffect: For each test candidate a new child of the currently considered state
             *              is generated. The solved constraint in the currently considered
             *              state is now labeled by true, which means, that the constraint
             *              already served to eliminate for the respective variable in this
             *              state.
             */
            void eliminate( vs::State* _currentState, const carl::Variable& _eliminationVar, const vs::Condition* _condition );
            
            /**
             * Applies the substitution of _currentState to the given conditions.
             * @param _currentState     The currently considered state.
             * @param _conditions       The conditions to which the substitution in this state
             *                          shall be applied. Note that these conditions are always
             *                          a subset of the condition vector in the father of this
             *                          state.
             * @sideeffect: The result is stored in the substitution result of the given state.
             */
            bool substituteAll( vs::State* _currentState, vs::ConditionList& _conditions );
            
            /**
             * Applies the substitution of the given state to all conditions, which were recently added to it.
             * @param _currentState The currently considered state.
             */
            void propagateNewConditions( vs::State* _currentState );
            
            /**
             * Inserts a state in the ranking.
             * @param _state The states, which will be inserted.
             */
            void addStateToRanking( vs::State* _state );
            
            /**
             * Inserts a state and all its successors in the ranking.
             * @param _state The root of the states, which will be inserted.
             */
            void addStatesToRanking( vs::State* _state );
            
            /**
             * Inserts all states with too high degree conditions being the given state or any of its successors in the ranking.
             * @param _state The root of the states, which will be inserted if they have too high degree conditions.
             */
            void insertTooHighDegreeStatesInRanking( vs::State* _state );
            
            /**
             * Removes a state from the ranking.
             * @param _state The states, which will be erased of the ranking.
             * @return  True, if the state was in the ranking.
             */
            bool removeStateFromRanking( vs::State& _state );
            
            /**
             * Removes a state and its successors from the ranking.
             * @param _state The root of the states, which will be erased of the ranking.
             */
            void removeStatesFromRanking( vs::State& _state );
            
            bool checkRanking() const;
            
            FormulasT getReasons( const carl::PointerSet<vs::Condition>& _conditions ) const;
            
            /**
             * 
             * @param _includeInconsistentTestCandidates
             */
            void updateInfeasibleSubset( bool _includeInconsistentTestCandidates = false );
            
            EvalRationalMap getIntervalAssignment( const vs::State* _state ) const;
            
            bool sideConditionsSatisfied( const vs::Substitution& _substitution, const EvalRationalMap& _assignment );
            
            bool solutionInDomain();
            
            /**
             * Finds all minimum covering sets of a vector of sets of sets. A minimum covering set
             * fulfills the following properties:
             *          1.) It covers in each set of sets at least one of its sets.
             *          2.) If you delete any element of the minimum covering set, the
             *              first property does not hold anymore.
             * @param _conflictSets     The vector of sets of sets, for which the method finds all minimum covering sets.
             * @param _minCovSets   The resulting minimum covering sets.
             */
            static void allMinimumCoveringSets( const vs::ConditionSetSetSet& _conflictSets, vs::ConditionSetSet& _minCovSets );
            
            /**
             * Adapts the passed formula according to the conditions of the currently considered state.
             * @param _state
             * @param _formulaCondMap
             * @return  true,   if the passed formula has been changed;
             *          false,  otherwise.
             */
            bool adaptPassedFormula( const vs::State& _state, FormulaConditionMap& _formulaCondMap );
            
            /**
             * Run the backend solvers on the conditions of the given state.
             * @param _state    The state to check the conditions of.
             * @return  True,    if the conditions are consistent and there is no unfinished ancestor;
             *          False,   if the conditions are inconsistent;
             *          Unknown, if the theory solver cannot give an answer for these conditons.
            */
            Answer runBackendSolvers( vs::State* _state );
            
            /**
             * Checks the correctness of the symbolic assignment given by the path from the root
             * state to the satisfying state.
             */
            void checkAnswer() const;
            
            /**
             * Checks whether the set of conditions is is consistent/inconsistent.
             * @param _state
             * @param _assumption
             * @param _description
             */
            void logConditions( const vs::State& _state, bool _assumption, const std::string& _description ) const;
            
        public:
            
            /**
             * Prints the history to the output stream.
             * @param _init The beginning of each row.
             * @param _out The output stream where the history should be printed.
             */
            void printAll( const std::string& _init = "", std::ostream& _out = std::cout ) const;
            
            /**
             * Prints the history to the output stream.
             * @param _init The beginning of each row.
             * @param _out The output stream where the history should be printed.
             */
            void printFormulaConditionMap( const std::string& _init = "", std::ostream& _out = std::cout ) const;
            
            /**
             * Prints the history to the output stream.
             * @param _init The beginning of each row.
             * @param _out The output stream where the history should be printed.
             */
            void printRanking( const std::string& _init = "", std::ostream& _out = std::cout ) const;
            
            /**
             * Prints the answer if existent.
             * @param _init The beginning of each row.
             * @param _out The output stream where the answer should be printed.
             */
            void printAnswer( const std::string& _init = "", std::ostream& _out = std::cout ) const;
    };

}    // end namespace smtrat

#include "VSModule.tpp"

