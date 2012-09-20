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
 * @file   UnivariateCADModule.h
 *
 * @author Ulrich Loup
 * @since 2012-01-19
 * @version 2012-01-20
 *
 */
#ifndef SMTRAT_UNIVARIATECADMODULE_H
#define SMTRAT_UNIVARIATECADMODULE_H

#include "../Module.h"

#include <ginac/ginac.h>
#include <ginacra/ginacra.h>

namespace smtrat
{
    /**
     * Module invoking a CAD solver of the GiNaCRA library. The solver is only used with univariate polynomials.
     * If a polynomial with more than one variable is added, this module passes it on.
     *
     * @author Ulrich Loup
     * @since 2012-01-19
     * @version 2012-01-20
     *
     */
    class UnivariateCADModule:
        public Module
    {
        /// contains all variables of the occurring constraints
        vector<symbol> mVariables;
        /// for each variable (as ex), representation of the solution space containing all data relevant for univariate CAD computations
        std::map<GiNaC::ex, GiNaCRA::CAD, GiNaC::ex_is_less> mCADs;
        /// for each variable (as ex), the flag as to whether we need to check the satisfiability here
        std::map<GiNaC::ex, bool, GiNaC::ex_is_less> mCADsToCheck;
        /// for each variable (as ex), the TS constraints carrying this variable
        std::map<GiNaC::ex, std::set<const Formula*> > mSubformulaBuckets;
        /// for each variable (as ex), the GiNaCRA constraints carrying this variable
        std::map<GiNaC::ex, vector<GiNaCRA::Constraint>, GiNaC::ex_is_less> mConstraintsBuckets;
        /// stores the status of not knowing the satisfiability result of the constraints
        bool mIsUnknown;

        public:
            UnivariateCADModule( Manager* const _tsmanager, const Formula* const );

            virtual ~UnivariateCADModule();

            virtual bool assertSubformula( const Formula* const );
            virtual Answer isConsistent();
            virtual void popBacktrackPoint();

        private:
            const GiNaCRA::Constraint convertConstraint( const Constraint& );
    };

}    // namespace smtrat

#endif   /** UnivariateCADModule_H */
