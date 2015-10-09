/**
 * @file RatOne.cpp
 */

#include "CADOnly.h"
#include "config.h"

namespace smtrat
{

    CADOnly::CADOnly( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        size_t position = 0;
        position = addBackendIntoStrategyGraph( position, MT_CNFerModule );
        position = addBackendIntoStrategyGraph( position, MT_SATModule );
        position = addBackendIntoStrategyGraph( position, MT_CADModule );
    }

    CADOnly::~CADOnly(){}

}    // namespace smtrat
