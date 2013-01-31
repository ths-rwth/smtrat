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

#include <ginacra/settings.h>


namespace smtrat
{

    NRATSolver::NRATSolver( Formula* _inputFormula ):
        Manager( _inputFormula )
    {
        unsigned position = 0;
        #ifdef SMTRAT_ENABLE_Preprocessing
        position = rStrategyGraph().addModuleType( position, MT_Preprocessing );
        #else        
        position = rStrategyGraph().addModuleType( position, MT_CNFerModule );
        #endif
        position = rStrategyGraph().addModuleType( position, MT_SATModule );
        #ifdef SMTRAT_ENABLE_VRWModule
        position = rStrategyGraph().addModuleType( position, MT_VRWModule );
        #endif
        #ifdef SMTRAT_ENABLE_CacheModule
        //position = rStrategyGraph().addModuleType( position, MT_CacheModule );
        #endif
        #ifdef SMTRAT_ENABLE_LRAModule
        position = rStrategyGraph().addModuleType( position, MT_LRAModule );
        #endif
        #ifdef SMTRAT_ENABLE_GroebnerModule
        position = rStrategyGraph().addModuleType( position, MT_GroebnerModule );
        #endif
  
        #ifdef SMTRAT_ENABLE_VSModule
        position = rStrategyGraph().addModuleType( position, MT_VSModule );
        #endif

        #ifdef SMTRAT_ENABLE_CADModule
        position = rStrategyGraph().addModuleType( position, MT_CADModule );
        #endif

    }

    NRATSolver::~NRATSolver(){}

}    // namespace smtrat

