/**
 * @file RatOne.cpp
 */

#include "RatOne.h"
#include "config.h"

namespace smtrat
{

    RatOne::RatOne():
        Manager()
    {
        size_t position = 0;
        #ifdef SMTRAT_ENABLE_BVModule
        position = addBackendIntoStrategyGraph( position, MT_BVModule );
        #endif
        #ifdef SMTRAT_ENABLE_PreprocessingModule
        position = addBackendIntoStrategyGraph( position, MT_PreprocessingModule );
        #else
        #ifdef SMTRAT_ENABLE_CNFerModule
        position = addBackendIntoStrategyGraph( position, MT_CNFerModule );
        #endif
        #endif
        #ifdef SMTRAT_ENABLE_IntBlastModule
        position = addBackendIntoStrategyGraph( position, MT_IntBlastModule );
        #endif
	#ifdef SMTRAT_ENABLE_SATModule
        position = addBackendIntoStrategyGraph( position, MT_SATModule );
	#endif
        #ifdef SMTRAT_ENABLE_IntEqModule
//        position = addBackendIntoStrategyGraph( position, MT_IntEqModule );
        #endif
        #ifdef SMTRAT_ENABLE_FouMoModule
//        position = addBackendIntoStrategyGraph( position, MT_FouMoModule );
        #endif
        #ifdef SMTRAT_ENABLE_LRAModule
        position = addBackendIntoStrategyGraph( position, MT_LRAModule );
        #endif
        #ifdef SMTRAT_ENABLE_GroebnerModule
//        position = addBackendIntoStrategyGraph( position, MT_GroebnerModule );
        #endif
        #ifdef SMTRAT_ENABLE_VSModule
        position = addBackendIntoStrategyGraph( position, MT_VSModule );
        #endif
        #ifdef SMTRAT_ENABLE_CADModule
        position = addBackendIntoStrategyGraph( position, MT_CADModule );
        #endif
//        #endif
    }

    RatOne::~RatOne(){}

}    // namespace smtrat

