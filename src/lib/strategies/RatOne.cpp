/**
 * @file RatOne.cpp
 */

#include "RatOne.h"
#include "config.h"

namespace smtrat
{

    RatOne::RatOne( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        size_t position = 0;
        position = addBackendIntoStrategyGraph( position, MT_PreprocessingModule );
        position = addBackendIntoStrategyGraph( position, MT_SATModule );
        position = addBackendIntoStrategyGraph( position, MT_LRAModule );
        position = addBackendIntoStrategyGraph( position, MT_VSModule );
        position = addBackendIntoStrategyGraph( position, MT_CADModule );
    }

    RatOne::~RatOne(){}

}    // namespace smtrat

