/**
 * @file Verit_Backend.cpp
 *
 */
#include "Verit_Backend.h"

namespace smtrat
{

    Verit_Backend::Verit_Backend():
        Manager()
    {
        addBackendIntoStrategyGraph( 0, MT_SATModule, isCondition );
        addBackendIntoStrategyGraph( 1, MT_LRAModule, isCondition );
        addBackendIntoStrategyGraph( 2, MT_VSModule, isCondition );
        //addBackendIntoStrategyGraph( 1, MT_CADModule, isCondition );
    }

    Verit_Backend::~Verit_Backend(){}

}    // namespace smtrat