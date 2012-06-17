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
 * Since: 2012-01-18
 * Version: 2012-01-20
 */

#ifndef SMTRAT_GROEBNERMODULE_H
#define SMTRAT_GROEBNERMODULE_H

#include <ginac/ginac.h>
#include <ginacra/ginacra.h>

//#include <ginacra/mr/MultivariateIdeal.h>

#include <ginacra/mr/Buchberger.h>
#include "../Module.h"

namespace smtrat
{
	/**
	 * Only active if we check inequalities.
	 * AS_RECEIVED: Do not change the received inequalities.
	 * FULL_REDUCED: Pass the fully reduced received inequalities.
	 * REDUCED: Pass the reduced received inequalities.
	 * REDUCED_ONLYSTRICT: Pass the nonstrict inequalities reduced, the others unchanged
	 * FULL_REDUCED_ONLYNEW: Do only a full reduce on the newly added received inequalities.
	 */
	enum pass_inequalities { AS_RECEIVED, FULL_REDUCED, REDUCED, REDUCED_ONLYSTRICT, FULL_REDUCED_ONLYNEW };
	
    /**
     * A class to save the current state of a GroebnerModule.
     * Needed for backtracking-support
     */
    class GroebnerModuleState
    {
        public:
            GroebnerModuleState(){}
            GroebnerModuleState( const GiNaCRA::Buchberger<GiNaCRA::GradedLexicgraphic>& basis ):
                mBasis( basis )
            {}
            ~GroebnerModuleState(){}

            const GiNaCRA::Buchberger<GiNaCRA::GradedLexicgraphic>& getBasis() const
            {
                return mBasis;
            }

        protected:
            ///The state of the basis
            const GiNaCRA::Buchberger<GiNaCRA::GradedLexicgraphic> mBasis;
    };

    /**
     * A solver module based on Groebner basis
     *
     */
    class GroebnerModule:
        public Module
    {
        public:
            typedef GiNaCRA::GradedLexicgraphic              Order;
            typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;

            GroebnerModule( Manager* const , const Formula* const );
            virtual ~GroebnerModule();

            virtual bool assertSubFormula( const Formula* const );
            virtual Answer isConsistent();
            virtual void pushBacktrackPoint();
            virtual void popBacktrackPoint();
			void printStateHistory();

        protected:
            /// The current Groebner basis
            GiNaCRA::Buchberger<GiNaCRA::GradedLexicgraphic> mBasis;
            /// A list of variables to help define the simplified constraints
            GiNaC::symtab mListOfVariables;
            /// Saves the relevant history to support backtracking
            std::list<GroebnerModuleState> mStateHistory;
			
			bool mAddedEqualitySinceLastCheck;
			
            bool saveState();
			std::set<const Formula*> generateReasons(const GiNaCRA::BitVector& reasons);

        private:
            typedef Module super;
			
			static const bool getReasonsForInfeasibility = true;
			static const bool passWithMinimalReasons = true;
			static const bool checkInequalities = true;
			static const pass_inequalities passInequalities = FULL_REDUCED;
			static const bool checkInequalitiesForTrivialSumOfSquares = true;
			static const bool checkEqualitiesForTrivialSumOfSquares = true;
			

    };

}    // namespace smtrat
#endif   /** GROEBNERMODULE_H */
