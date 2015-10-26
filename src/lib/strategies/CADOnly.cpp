/**
 * @file RatOne.cpp
 */

#include "CADOnly.h"
#include "../modules/Modules.h"

namespace smtrat
{

    CADOnly::CADOnly( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        //size_t position = 0;
        //position = addBackendIntoStrategyGraph( position, MT_CNFerModule );
        //position = addBackendIntoStrategyGraph( position, MT_SATModule );
        //position = addBackendIntoStrategyGraph( position, MT_CADModule );
		
		setStrategy({
			addBackend<CNFerModule>({
				addBackend<SATModule<SATSettings1>>({
					addBackend<CADModule<CADSettings1>>()
				})
			})
		});
    }

    CADOnly::~CADOnly(){}

}    // namespace smtrat
