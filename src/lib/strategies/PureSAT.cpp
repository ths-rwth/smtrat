/**
 * @file RatOne.cpp
 */

#include "PureSAT.h"
#include "config.h"

namespace smtrat
{

    PureSAT::PureSAT( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        addBackendIntoStrategyGraph( 0, MT_SATModule );
    }

    PureSAT::~PureSAT(){}

}    // namespace smtrat
