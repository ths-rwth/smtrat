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

#ifndef SMTRAT_VSMODULE_H
#define SMTRAT_VSMODULE_H

#define VS_INCREMENTAL
#define VS_INFEASIBLE_SUBSET_GENERATION

//#define VS_STATISTICS
//#define VS_PRINT_ANSWERS
//#define VS_LOG_INTERMEDIATE_STEPS

#include "Substitute.h"
#include "State.h"
#include "VSSettings.h"
#include "../../Module.h"
#include "../../RuntimeSettings.h"

namespace smtrat
{
    template<class Settings>
    class VSModule: public Module
    {
        private:

            // Type and object definitions.
            
            typedef std::pair<size_t, std::pair<size_t, size_t> > UnsignedTriple;
            
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
            
            typedef std::pair<UnsignedTriple, vs::State*>                   ValStatePair;
            typedef std::map<UnsignedTriple, vs::State*, unsignedTripleCmp> ValuationMap;
            typedef std::map<const Formula* const, const vs::Condition*>    FormulaConditionMap;
            typedef std::vector<std::pair<carl::Variable,carl::Variable>>   VarNamePairVector;

            // Members.
            bool                        mConditionsChanged;
            bool                        mInconsistentConstraintAdded;
            size_t                      mIDCounter;
            #ifdef VS_STATISTICS
            size_t                      mStepCounter;
            #endif
            vs::State*                  mpStateTree;
            Variables                   mAllVariables;
            FormulaConditionMap         mFormulaConditionMap;
            ValuationMap                mRanking;
            mutable VarNamePairVector   mVariableVector;

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
            double rateCall( const PointerSet<Formula>& ) const;

            // Printing methods.
            void printAll( const std::string& = "", std::ostream& = std::cout ) const;
            void printFormulaConditionMap( const std::string& = "", std::ostream& = std::cout ) const;
            void printRanking( const std::string& = "", std::ostream& = std::cout ) const;
            void printAnswer( const std::string& = "", std::ostream& = std::cout ) const;

        private:

            // Some more type definitions.
            typedef std::pair<vs::Substitution, std::list< vs::State* >> ChildrenGroup;
            typedef std::vector<ChildrenGroup>                   ChildrenGroups;

            // Methods.
            void increaseIDCounter()
            {
                assert( mIDCounter < UINT_MAX );
                mIDCounter++;
            }
            
            inline Answer consistencyTrue();
            
            void eliminate( vs::State*, const carl::Variable&, const vs::Condition* );
            bool substituteAll( vs::State*, vs::ConditionList& );
            void propagateNewConditions( vs::State* );
            void addStateToRanking( vs::State* );
            void addStatesToRanking( vs::State* );
            void insertTooHighDegreeStatesInRanking( vs::State* );
            bool removeStateFromRanking( vs::State& );
            void removeStatesFromRanking( vs::State& );
            PointerSet<Formula> getReasons( const PointerSet<vs::Condition>& _conditions ) const;
            void updateInfeasibleSubset( bool = false );
            EvalRationalMap getIntervalAssignment( const vs::State* _state ) const;
            bool solutionInDomain();
            static void allMinimumCoveringSets( const vs::ConditionSetSetSet&, vs::ConditionSetSet& );
            bool adaptPassedFormula( const vs::State&, FormulaConditionMap& );
            Answer runBackendSolvers( vs::State* );
            #ifdef VS_LOG_INTERMEDIATE_STEPS
            void checkAnswer() const;
            void logConditions( const vs::State&, bool, const std::string& ) const;
            #endif
    };

}    // end namespace smtrat

#include "VSModule.tpp"

#endif   /** VSMODULE_H */
