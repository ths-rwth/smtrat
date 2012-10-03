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

#ifdef USE_GB

#include <ginacra/settings.h>

#endif

namespace smtrat
{

    NRATSolver::NRATSolver( Formula* _inputFormula ):
        Manager( _inputFormula )
    {
        #ifdef USE_GB
        GiNaCRA::MultivariatePolynomialSettings::InitializeGiNaCRAMultivariateMR();
        #endif

        unsigned position = 0;
        position = rStrategyGraph().addModuleType( position, MT_CNFerModule );
        position = rStrategyGraph().addModuleType( position, MT_PreProModule );
        position = rStrategyGraph().addModuleType( position, MT_SATModule );
        position = rStrategyGraph().addModuleType( position, MT_LRAModule );
        #ifdef USE_GB
        position = rStrategyGraph().addModuleType( position, MT_GroebnerModule );
        position = rStrategyGraph().addModuleType( position, MT_VSModule );
        #else
        position = rStrategyGraph().addModuleType( position, MT_VSModule );
        #endif
        #ifdef USE_CAD
        position = rStrategyGraph().addModuleType( position, MT_CADModule );
        #endif

    }

    NRATSolver::~NRATSolver(){}

}    // namespace smtrat

