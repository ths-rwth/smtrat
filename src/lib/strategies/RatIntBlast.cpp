/**
 * @file RatIntBlast.cpp
 */

#include "RatIntBlast.h"
#include "config.h"

namespace smtrat
{

    RatIntBlast::RatIntBlast( bool _externalModuleFactoryAdding ):
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
        #ifdef SMTRAT_ENABLE_IntBlastModule
        position = addBackendIntoStrategyGraph( position, MT_IntBlastModule );
        #endif
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

    RatIntBlast::~RatIntBlast(){}

}    // namespace smtrat

