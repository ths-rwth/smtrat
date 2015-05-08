/**
 * @file StrategyOne.cpp
 *
 */
#include "StrategyOne.h"

namespace smtrat
{

    StrategyOne::StrategyOne():
        Manager()
    {
        addBackendIntoStrategyGraph( 0, MT_CNFerModule, isCondition );
        addBackendIntoStrategyGraph( 1, MT_PreprocessingModule, isCondition );
        addBackendIntoStrategyGraph( 2, MT_SATModule, isCondition );
        addBackendIntoStrategyGraph( 3, MT_LRAModule, isCondition );
        addBackendIntoStrategyGraph( 4, MT_VSModule, isCondition );
        addBackendIntoStrategyGraph( 5, MT_CADModule, isCondition );
        addBackendIntoStrategyGraph( 4, MT_CADModule, isCondition );
    }

    StrategyOne::~StrategyOne(){}

}    // namespace smtrat