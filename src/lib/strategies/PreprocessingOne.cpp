/**
 * @file PreprocessingOne.cpp
 */

#include "PreprocessingOne.h"
#include "config.h"

namespace smtrat
{

    static bool conditionEvaluation0( carl::Condition _condition )
    {
        return carl::PROP_TRUE <= _condition;
    }
    
    PreprocessingOne::PreprocessingOne( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        size_t position = 0;
        position = addBackendIntoStrategyGraph( position, MT_EMModule, conditionEvaluation0 );
        position = addBackendIntoStrategyGraph( position, MT_RPFModule, conditionEvaluation0 );
        position = addBackendIntoStrategyGraph( position, MT_SplitSOSModule, conditionEvaluation0 );
        position = addBackendIntoStrategyGraph( position, MT_ESModule, conditionEvaluation0 );
        position = addBackendIntoStrategyGraph( position, MT_BEModule, conditionEvaluation0 );
        position = addBackendIntoStrategyGraph( position, MT_CBModule, conditionEvaluation0 );
    }

    PreprocessingOne::~PreprocessingOne(){}

}    // namespace smtrat
