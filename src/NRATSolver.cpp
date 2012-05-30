/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * @file NRATSolver.cpp
 *
 */

#include "NRATSolver.h"

namespace smtrat
{
    NRATSolver::NRATSolver( Formula* _inputFormula ):
        Manager( _inputFormula )
    {
        /*
                strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_SIMPLIFIERMODULE, MT_VSModule );
                strategy().addModuleType( PROP_TRUE, MT_SimplifierModule );
        */

        //        strategy().addModuleType( PROP_TRUE, MT_SATModule );
        //

        /*
                strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_SIMPLIFIERMODULE, MT_VSModule );
                strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_SATMODULE, MT_SimplifierModule );
        */
        strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_SATMODULE, MT_VSModule );
        strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_CNFERMODULE, MT_SATModule );
        strategy().addModuleType( PROP_TRUE, MT_CNFerModule );

        //        strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_UNIVARIATECADMODULE, MT_CADModule );

        //        strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_UNIVARIATECADMODULE, MT_CADModule );
        //        strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_VSMODULE, MT_UnivariateCADModule );
        //        strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_VSMODULE, MT_CADModule );
        //        strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_GROEBNERMODULE, MT_VSModule );
        //        strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_SIMPLIFIERMODULE, MT_VSModule );
        //        strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_SIMPLIFIERMODULE, MT_GroebnerModule );
        //        strategy().addModuleType( PROP_TRUE, MT_SimplifierModule );
        //        strategy().addModuleType( PROP_TRUE, MT_CADModule );
    }

    NRATSolver::~NRATSolver(){}

}    // namespace smtrat

