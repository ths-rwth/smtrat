/**
 * @file RatOne.cpp
 */

#include "PureSAT.h"
#include "config.h"

namespace smtrat
{

    PureSAT::PureSAT():
        Manager()
    {
        addBackendIntoStrategyGraph( 0, MT_SATModule );
    }

    PureSAT::~PureSAT(){}

}    // namespace smtrat
