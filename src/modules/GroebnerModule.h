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
 * InequalitiesRow
 * InequalitiesTable
 * GroebnerModule
 *
 * Since: 2012-01-18
 * Version: 2012-06-20
 */

#ifndef SMTRAT_GROEBNERMODULE_H
#define SMTRAT_GROEBNERMODULE_H

#include <ginac/ginac.h>
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
			const std::vector<unsigned> mVariablesInEqualities;
    };

	class GroebnerModule;
	
	/**
	 * A row in the InequalitiesTable. A row basically represents an inequality.
	 */
	class InequalitiesRow {
		typedef GBSettings::Polynomial Polynomial;
		typedef GBSettings::MultivariateIdeal Ideal;
		typedef GBSettings::Reductor Reductor;
		
	public:
		InequalitiesRow(GroebnerModule*, const Formula* const received, unsigned btpoint) ;
		
		Answer reduceWithGb(const Ideal& gb, unsigned btpoint);
		
		bool popBacktrackPoint(unsigned btp);
		
		void print(std::ostream& os = std::cout ) const;
	protected:
		const Formula* receivedFormulaEntry;
		Constraint_Relation relation;
		Formula::const_iterator passedFormulaEntry;
		std::list<std::pair<unsigned,Polynomial> > reductions;
		GroebnerModule* mModule;
	};
	

	/**
	 * A table of all inequalities and how they are reduced.
	 */
	class InequalitiesTable {
		
		typedef GBSettings::Polynomial Polynomial;
		typedef GBSettings::MultivariateIdeal Ideal;
	public: 
		InequalitiesTable(GroebnerModule*  module);
		
		void InsertReceivedFormula(const Formula* const received );
		
		void pushBacktrackPoint() ;
		
		void popBacktrackPoint() ;
		
		void reduceWRTGroebnerBasis(const Ideal& gb);
		
		void print(std::ostream& os= std::cout) const;
		
		std::list<size_t> mNrInequalitiesForBtPoints;
		std::vector<InequalitiesRow> mReducedInequalities;
		
	
		GroebnerModule*  mModule;
	};
	
	
    /**
     * A solver module based on Groebner basis
     *
     */
    class GroebnerModule:
        public Module
    {
		typedef GBSettings Settings;
		
		friend InequalitiesTable;
		friend InequalitiesRow;
		
        public:
            typedef Settings::Order              Order;
            typedef Settings::Polynomial		 Polynomial;

            GroebnerModule( Manager* const , const Formula* const );
            virtual ~GroebnerModule();

            virtual bool assertSubFormula( const Formula* const );
            virtual Answer isConsistent();
            virtual void pushBacktrackPoint();
            virtual void popBacktrackPoint();
			void printStateHistory();

        protected:
			//TODO just take the last one from the state history?
            /// The current Groebner basis
            GiNaCRA::Buchberger<Settings::Order> mBasis;
            /// A list of variables to help define the simplified constraints
            GiNaC::symtab mListOfVariables;
            /// Saves the relevant history to support backtracking
            std::list<GroebnerModuleState> mStateHistory;
			
			InequalitiesTable mInequalities;
			
			std::set<unsigned> mVariablesInEqualities;
			
			bool mPopCausesRecalc;
			
            bool saveState();
			std::set<const Formula*> generateReasons(const GiNaCRA::BitVector& reasons);
			void passGB();

			void removeSubformulaFromPassedFormula(const Formula&);
        private:
            typedef Module super;
			
			
			static const bool gatherStatistics = false;

    };
	
	

}    // namespace smtrat
#endif   /** GROEBNERMODULE_H */
