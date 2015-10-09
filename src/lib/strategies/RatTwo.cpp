/**
 * @file RatTwo.cpp
 */

#include "RatTwo.h"
#include "config.h"

namespace smtrat
{

    RatTwo::RatTwo( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        size_t position = 0;
        position = addBackendIntoStrategyGraph( position, MT_PreprocessingModule );
        position = addBackendIntoStrategyGraph( position, MT_SATModule );
        position = addBackendIntoStrategyGraph( position, MT_ICPModule );
        position = addBackendIntoStrategyGraph( position, MT_VSModule );
        position = addBackendIntoStrategyGraph( position, MT_CADModule );
    }

    RatTwo::~RatTwo(){}

}    // namespace smtrat

