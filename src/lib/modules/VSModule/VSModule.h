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
            typedef std::pair<vs::UnsignedTriple, vs::State*>                       ValStatePair;
            typedef std::map<vs::UnsignedTriple, vs::State*, vs::unsignedTripleCmp> ValuationMap;
            typedef std::map<const Formula* const, const vs::Condition*>            FormulaConditionMap;
            typedef std::vector<std::pair<carl::Variable,carl::Variable>>           VarNamePairVector;

            // Members.
            bool                mConditionsChanged;
            bool                mInconsistentConstraintAdded;
            unsigned            mIDCounter;
            #ifdef VS_STATISTICS
            unsigned            mStepCounter;
            #endif
            vs::State*          mpStateTree;
            Variables           mAllVariables;
            FormulaConditionMap mFormulaConditionMap;
            ValuationMap        mRanking;
            VarNamePairVector   mVariableVector;

        public:

            // Constructors.
            VSModule( ModuleType _type, const Formula* const, RuntimeSettings*, Conditionals&, Manager* const = NULL );

            // Destructor.
            ~VSModule();
            
            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );
            void updateModel();

            // Printing methods.
            void printAll( const std::string& = "", std::ostream& = std::cout ) const;
            void printFormulaConditionMap( const std::string& = "", std::ostream& = std::cout ) const;
            void printRanking( const std::string& = "", std::ostream& = std::cout ) const;
            void printAnswer( const std::string& = "", std::ostream& = std::cout ) const;

        private:

            // Some more type definitions.
            typedef std::pair<vs::Substitution, vs::StateVector> ChildrenGroup;
            typedef std::vector<ChildrenGroup>                   ChildrenGroups;

            // Methods.
            void increaseIDCounter()
            {
                assert( mIDCounter < UINT_MAX );
                mIDCounter++;
            }
            
            void eliminate( vs::State*, const std::string&, const vs::Condition* );
            bool substituteAll( vs::State*, vs::ConditionList& );
            void propagateNewConditions( vs::State* );
            void insertDTinRanking( vs::State* );
            void insertDTsinRanking( vs::State* );
            bool eraseDTofRanking( vs::State& );
            void eraseDTsOfRanking( vs::State& );
            void updateInfeasibleSubset( bool = false );
            std::vector<std::pair<std::string, std::pair<vs::Substitution::Type, vs::SqrtEx> > > getSymbolicAssignment() const;
            static void allMinimumCoveringSets( const vs::ConditionSetSetSet&, vs::ConditionSetSet& );
            bool adaptPassedFormula( const vs::State&, FormulaConditionMap&, bool = false );
            Answer runBackendSolvers( vs::State*, bool = false );
            #ifdef VS_LOG_INTERMEDIATE_STEPS
            void checkAnswer() const;
            void logConditions( const vs::State&, bool, const std::string& ) const;
            #endif
    };

}    // end namespace smtrat

#include "VSModule.tpp"

#endif   /** VSMODULE_H */
