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
 * @file   GroebnerModule.h
 *
 * @author Sebastian Junges
 *
 * Note: This file might be a little messy to the reader at first. For efficiency reasons however,
 * there is some cross-reference  between the datastructure and the module.
 *
 * The classes contained in here are
 * GroebnerModuleState
 * InequalitiesTable
 * GroebnerModule
 *
 * Since: 2012-01-18
 * Version: 2012-06-20
 */

#ifndef SMTRAT_GROEBNERMODULE_H
#define SMTRAT_GROEBNERMODULE_H

#include <ginacra/ginacra.h>

//#include <ginacra/mr/MultivariateIdeal.h>

#include <ginacra/mr/Buchberger.h>
#include "../Module.h"
#include "GBModule/InequalitiesTable.h"

namespace smtrat
{
    /**
     * A class to save the current state of a GroebnerModule.
     * Needed for backtracking-support
     */
    class GroebnerModuleState
    {
        public:
            GroebnerModuleState(){}
            GroebnerModuleState( const GiNaCRA::Buchberger<GBSettings::Order>& basis ):
                mBasis( basis )
            {}
            ~GroebnerModuleState(){}

            const GiNaCRA::Buchberger<GBSettings::Order>& getBasis() const
            {
                return mBasis;
            }

        protected:
            ///The state of the basis
            const GiNaCRA::Buchberger<GBSettings::Order> mBasis;
    };

    class GroebnerModule;

    struct FormulaConstraintCompare
    {
        bool operator ()( const Formula::const_iterator& c1, const Formula::const_iterator& c2 ) const
        {
            return ((*c1)->constraint() < (*c2)->constraint());
        }
    };

    /**
     * A table of all inequalities and how they are reduced.
     */
    class InequalitiesTable
    {
        typedef GBSettings::Polynomial                                                    Polynomial;
        typedef GBSettings::MultivariateIdeal                                             Ideal;
        public:
			
			typedef std::pair<unsigned, Polynomial>                                           CellEntry;
			typedef std::tuple<Formula::iterator, Constraint_Relation, std::list<CellEntry> > RowEntry;
			typedef std::map<Formula::const_iterator, RowEntry, FormulaConstraintCompare>     Rows;
			typedef std::pair<Formula::const_iterator, RowEntry>                              Row;
			
            InequalitiesTable( GroebnerModule* module );

            Rows::iterator InsertReceivedFormula( Formula::const_iterator received );

            void pushBacktrackPoint();

            void popBacktrackPoint( unsigned nrBacktracks );

            Answer reduceWRTGroebnerBasis( const Ideal& gb );
			bool reduceWRTGroebnerBasis( Rows::iterator, const Ideal& gb );
			Answer reduceWRTGroebnerBasis( const std::list<Rows::iterator>& ineqToBeReduced, const Ideal& gb );

            void removeInequality( Formula::const_iterator _formula );

            void print( std::ostream& os = std::cout ) const;

            Rows            mReducedInequalities;

            unsigned        mBtnumber;
            GroebnerModule* mModule;

            Rows::iterator  mNewConstraints;
            unsigned        mLastRestart;
			

     
    };

    /**
     * A solver module based on Groebner basis
     *
     */
    class GroebnerModule:
        public Module
    {
        typedef GBSettings Settings;

        friend class InequalitiesTable;

        public:
            typedef Settings::Order      Order;
            typedef Settings::Polynomial Polynomial;

            GroebnerModule( Manager* const , const Formula* const );
            virtual ~GroebnerModule();

            bool assertSubformula( Formula::const_iterator _formula );
            virtual Answer isConsistent();
            void removeSubformula( Formula::const_iterator _formula );
            void printStateHistory();

        protected:
            //TODO just take the last one from the state history?
            /// The current Groebner basis
            GiNaCRA::Buchberger<Settings::Order> mBasis;
            /// A list of variables to help define the simplified constraints
            GiNaC::symtab mListOfVariables;
            /// Saves the relevant history to support backtracking
            std::list<GroebnerModuleState>       mStateHistory;

            InequalitiesTable                    mInequalities;

            std::set<unsigned>                   mVariablesInEqualities;

            std::vector<Formula::const_iterator> mBacktrackPoints;

            bool                                 mPopCausesRecalc;
			
			std::list<InequalitiesTable::Rows::iterator>		 mNewInequalities;
			
			std::map<unsigned, unsigned>         mAdditionalVarMap;

            void pushBacktrackPoint( Formula::const_iterator btpoint );
            void popBacktrackPoint( Formula::const_iterator btpoint );
            bool saveState();
            std::set<const Formula*> generateReasons( const GiNaCRA::BitVector& reasons );
            void passGB();
			Polynomial transformIntoEquality( Formula::const_iterator constraint );

            void removeSubformulaFromPassedFormula( Formula::iterator _formula );
            bool validityCheck();

        private:
            typedef Module    super;

            static const bool gatherStatistics = false;

    };

}    // namespace smtrat
#endif   /** GROEBNERMODULE_H */
