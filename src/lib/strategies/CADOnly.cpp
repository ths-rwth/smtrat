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
	    #ifdef SMTRAT_ENABLE_CNFerModule
        position = addBackendIntoStrategyGraph( position, MT_CNFerModule );
	    #endif
	    #ifdef SMTRAT_ENABLE_SATModule
        position = addBackendIntoStrategyGraph( position, MT_SATModule );
	    #endif
        #ifdef SMTRAT_ENABLE_CADModule
        position = addBackendIntoStrategyGraph( position, MT_CADModule );
        #endif
//        #endif
    }

    CADOnly::~CADOnly(){}

}    // namespace smtrat
