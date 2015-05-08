/**
 * @file NRATSolverCAD.cpp
 *
 */

#include "NRATSolverCAD.h"
#include "config.h"

namespace smtrat
{

    NRATSolverCAD::NRATSolverCAD():
        Manager()
    {
        unsigned position = 0;
        #ifdef SMTRAT_ENABLE_Preprocessing
        position = addBackendIntoStrategyGraph( position, MT_Preprocessing );
        #else
        position = addBackendIntoStrategyGraph( position, MT_CNFerModule );
        #endif
        position = addBackendIntoStrategyGraph( position, MT_SATModule );

        #ifdef SMTRAT_ENABLE_LRAModule
        position = addBackendIntoStrategyGraph( position, MT_LRAModule );
        #endif
        #ifdef SMTRAT_ENABLE_VSModule
        position = addBackendIntoStrategyGraph( position, MT_VSModule );
        #endif
        #ifdef SMTRAT_ENABLE_CADModule
        position = addBackendIntoStrategyGraph( position, MT_CADModule );
        #endif
    }

    NRATSolverCAD::~NRATSolverCAD(){}

}    // namespace smtrat

