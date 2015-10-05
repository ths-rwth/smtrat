/**
 * @file RatICP.cpp
 */

#include "RatICP.h"
#include "config.h"

namespace smtrat
{

    RatICP::RatICP( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        size_t position = 0;
        #ifdef SMTRAT_ENABLE_PreprocessingModule
        position = addBackendIntoStrategyGraph( position, MT_PreprocessingModule );
        #else
        #ifdef SMTRAT_ENABLE_CNFerModule
        position = addBackendIntoStrategyGraph( position, MT_CNFerModule );
        #endif
        #endif
        #ifdef SMTRAT_ENABLE_SATModule
        position = addBackendIntoStrategyGraph( position, MT_SATModule );
        #endif
        #ifdef SMTRAT_ENABLE_ICPModule
        position = addBackendIntoStrategyGraph( position, MT_ICPModule );
        #endif
    }

    RatICP::~RatICP(){}

}    // namespace smtrat

