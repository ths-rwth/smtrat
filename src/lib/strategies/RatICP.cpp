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
        position = addBackendIntoStrategyGraph( position, MT_PreprocessingModule );
        position = addBackendIntoStrategyGraph( position, MT_SATModule );
        position = addBackendIntoStrategyGraph( position, MT_ICPModule );
    }

    RatICP::~RatICP(){}

}    // namespace smtrat

