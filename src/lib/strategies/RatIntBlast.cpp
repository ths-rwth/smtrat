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
//        position = addBackendIntoStrategyGraph( position, MT_PreprocessingModule );
//        position = addBackendIntoStrategyGraph( position, MT_IncWidthModule );
//        position = addBackendIntoStrategyGraph( position, MT_SATModule );
        position = addBackendIntoStrategyGraph( position, MT_IntBlastModule );
    }

    RatIntBlast::~RatIntBlast(){}

}    // namespace smtrat

