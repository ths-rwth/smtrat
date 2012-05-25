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
 * @file   CADModule.h
 *
 * @author Ulrich Loup
 * @since 2012-02-04
 * @version 2012-05-21
 *
 */
#ifndef SMTRAT_CADMODULE_H
#define SMTRAT_CADMODULE_H

#include "../Module.h"

#include <unordered_map>
#include <ginac/ginac.h>
#include <ginacra/ginacra.h>

namespace smtrat
{
    /**
     * Module invoking a CAD solver of the GiNaCRA library. The solver is only used with univariate polynomials.
     * If a polynomial with more than one variable is added, this module passes it on.
     *
     * @author Ulrich Loup
     * @since 2012-02-04
     * @version 2012-04-09
     *
     */
    class CADModule:
        public Module
    {
        /// representation of the solution space containing all data relevant for CAD computations
        GiNaCRA::CAD mCAD;
        /// the GiNaCRA constraints corresponding to received constraints
        vector<GiNaCRA::Constraint> mConstraints;

        public:
            CADModule( Manager* const _tsmanager, const Formula* const );

            virtual ~CADModule();

            virtual bool assertSubFormula( const Formula* const );
            virtual Answer isConsistent();
            virtual void popBacktrackPoint();

        private:
            const GiNaCRA::Constraint convertConstraint( const Constraint& );
    };

}    // namespace smtrat
#endif   /** CADMODULE_H */
