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
    static bool caseOne ( Condition _condition )
    {
        return PROP_CANNOT_BE_SOLVED_BY_VSMODULE <= _condition;
    }
    #ifdef USE_GB
    static bool caseTwo ( Condition _condition )
    {
        return PROP_CANNOT_BE_SOLVED_BY_GROEBNERMODULE <= _condition;
    }
    #endif
    static bool caseThree ( Condition _condition )
    {
        return PROP_CANNOT_BE_SOLVED_BY_SATMODULE <= _condition;
    }
    static bool caseFour ( Condition _condition )
    {
        return PROP_CANNOT_BE_SOLVED_BY_CNFERMODULE <= _condition;
    }
    static bool caseFive ( Condition _condition )
    {
        return PROP_CANNOT_BE_SOLVED_BY_PREPROMODULE <= _condition;
    }
    static bool caseSix ( Condition _condition )
    {
        return !(PROP_CANNOT_BE_SOLVED_BY_VSMODULE <= _condition);
    }

    NRATSolver::NRATSolver( Formula* _inputFormula ) : Manager( _inputFormula )
    {
		#ifdef USE_GB
        GiNaCRA::MultivariatePolynomialSettings::InitializeGiNaCRAMultivariateMR();
		#endif
		#ifdef USE_CAD
		strategy().addModuleType( caseOne, MT_CADModule );
		#endif
		#ifdef USE_GB
		strategy().addModuleType( caseTwo, MT_VSModule );
		strategy().addModuleType( caseThree, MT_GroebnerModule);
		#else
		strategy().addModuleType( caseThree, MT_VSModule );
		#endif
		strategy().addModuleType( caseFour, MT_SATModule );
        strategy().addModuleType( caseFive, MT_CNFerModule );
        strategy().addModuleType( caseSix, MT_PreProModule );
    }

    NRATSolver::~NRATSolver() {}

}    // namespace smtrat
