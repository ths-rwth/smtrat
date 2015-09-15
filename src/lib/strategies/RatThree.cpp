/**
 * @file RatThree.cpp
 *
 */
#include "RatThree.h"

namespace smtrat
{

    RatThree::RatThree( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        addBackendIntoStrategyGraph( 0, MT_CNFerModule, isCondition );
        addBackendIntoStrategyGraph( 1, MT_PreprocessingModule, isCondition );
        addBackendIntoStrategyGraph( 2, MT_SATModule, isCondition );
        addBackendIntoStrategyGraph( 3, MT_LRAModule, isCondition );
        addBackendIntoStrategyGraph( 4, MT_VSModule, isCondition );
        addBackendIntoStrategyGraph( 5, MT_CADModule, isCondition );
        addBackendIntoStrategyGraph( 4, MT_CADModule, isCondition );
    }

    RatThree::~RatThree(){}

}    // namespace smtrat