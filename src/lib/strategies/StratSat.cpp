/**
 * @file StratSat.cpp
 */

#include "StratSat.h"
#include "config.h"

namespace smtrat
{

	StratSat::StratSat() :
        Manager()
    {
        addBackendIntoStrategyGraph( 0, MT_CNFerModule );
        addBackendIntoStrategyGraph( 1, MT_SATModule );
    }

	StratSat::~StratSat(){}

}    // namespace smtrat

