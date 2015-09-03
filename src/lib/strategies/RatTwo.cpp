/**
 * @file RatTwo.cpp
 */

#include "RatTwo.h"
#include "config.h"

namespace smtrat
{

    RatTwo::RatTwo():
        Manager()
    {
        size_t position = 0;
        #ifdef SMTRAT_ENABLE_CNFerModule
        position = addBackendIntoStrategyGraph( position, MT_CNFerModule );
        #endif
        #ifdef SMTRAT_ENABLE_PreprocessingModule
        position = addBackendIntoStrategyGraph( position, MT_PreprocessingModule );
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
        #ifdef SMTRAT_ENABLE_ICPModule
        position = addBackendIntoStrategyGraph( position, MT_ICPModule );
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

    RatTwo::~RatTwo(){}

}    // namespace smtrat

