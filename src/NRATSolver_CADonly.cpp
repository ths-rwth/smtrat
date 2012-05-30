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
 * @file NRATSolver_CADonly.cpp
 * @author Ulrich Loup
 * @since 2012-03-21
 * @version 2012-05-21
 */

#include "NRATSolver_CADonly.h"

namespace smtrat
{
    NRATSolver_CADonly::NRATSolver_CADonly( Formula* _inputFormula ):
        Manager( _inputFormula )
    {
        //        strategy().addModuleType( PROP_CANNOT_BE_SOLVED_BY_UNIVARIATECADMODULE, MT_CADModule );
        strategy().addModuleType( PROP_TRUE, MT_CADModule );
    }

    NRATSolver_CADonly::~NRATSolver_CADonly(){}

}    // namespace smtrat

