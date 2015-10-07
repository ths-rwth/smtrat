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
        position = addBackendIntoStrategyGraph( position, MT_PreprocessingModule );
        position = addBackendIntoStrategyGraph( position, MT_SATModule );
        // position = addBackendIntoStrategyGraph( position, MT_ICPModule );
        position = addBackendIntoStrategyGraph( position, MT_IntBlastModule );
//        position = addBackendIntoStrategyGraph( position, MT_CNFerModule );
//        position = addBackendIntoStrategyGraph( position, MT_SATModule );
        position = addBackendIntoStrategyGraph( position, MT_LRAModule );
        position = addBackendIntoStrategyGraph( position, MT_VSModule );
        position = addBackendIntoStrategyGraph( position, MT_CADModule );
    }

    RatIntBlast::~RatIntBlast(){}

}    // namespace smtrat

