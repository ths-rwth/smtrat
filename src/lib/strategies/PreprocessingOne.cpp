/**
 * @file PreprocessingOne.cpp
 */

#include "PreprocessingOne.h"
#include "config.h"

namespace smtrat
{
    
    PreprocessingOne::PreprocessingOne( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        size_t position = 0;
        position = addBackendIntoStrategyGraph( position, MT_EMModule );
        position = addBackendIntoStrategyGraph( position, MT_RPFModule );
        position = addBackendIntoStrategyGraph( position, MT_SplitSOSModule );
        position = addBackendIntoStrategyGraph( position, MT_ESModule );
        position = addBackendIntoStrategyGraph( position, MT_BEModule );
        position = addBackendIntoStrategyGraph( position, MT_CBModule );
    }

    PreprocessingOne::~PreprocessingOne(){}

}    // namespace smtrat
