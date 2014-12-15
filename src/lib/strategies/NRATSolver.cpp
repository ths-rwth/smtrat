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
#include "config.h"

namespace smtrat
{

    NRATSolver::NRATSolver():
        Manager()
    {
        size_t position = 0;
        #ifdef SMTRAT_ENABLE_Preprocessing
        position = addBackendIntoStrategyGraph( position, MT_Preprocessing );
        #else
        position = addBackendIntoStrategyGraph( position, MT_CNFerModule );
        #endif
        position = addBackendIntoStrategyGraph( position, MT_SATModule );
//        #ifdef SMTRAT_ENABLE_ReduceModule
//        position = addBackendIntoStrategyGraph( position, MT_ReduceModule );
//        #else
        #ifdef SMTRAT_ENABLE_VRWModule
        position = addBackendIntoStrategyGraph( position, MT_VRWModule );
        #endif
        #ifdef SMTRAT_ENABLE_CacheModule
        //position = addBackendIntoStrategyGraph( position, MT_CacheModule );
        #endif
        #ifdef SMTRAT_ENABLE_IntEqModule
        position = addBackendIntoStrategyGraph( position, MT_IntEqModule );
        #endif
        #ifdef SMTRAT_ENABLE_FouMoModule
        position = addBackendIntoStrategyGraph( position, MT_FouMoModule );
        #endif
        #ifdef SMTRAT_ENABLE_LRAModule
        position = addBackendIntoStrategyGraph( position, MT_LRAModule );
        #endif
        #ifdef SMTRAT_ENABLE_GroebnerModule
        position = addBackendIntoStrategyGraph( position, MT_GroebnerModule );
        #endif
        #ifdef SMTRAT_ENABLE_VSModule
        position = addBackendIntoStrategyGraph( position, MT_VSModule );
        #endif
        #ifdef SMTRAT_ENABLE_CADModule
        position = addBackendIntoStrategyGraph( position, MT_CADModule );
        #endif
//        #endif
    }

    NRATSolver::~NRATSolver(){}

}    // namespace smtrat

