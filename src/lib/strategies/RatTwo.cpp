/**
 * @file RatTwo.cpp
 */

#include "RatTwo.h"
#include "../modules/Modules.h"

namespace smtrat
{

    RatTwo::RatTwo( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        //size_t position = 0;
        //position = addBackendIntoStrategyGraph( position, MT_PreprocessingModule );
        //position = addBackendIntoStrategyGraph( position, MT_SATModule );
        //position = addBackendIntoStrategyGraph( position, MT_ICPModule );
        //position = addBackendIntoStrategyGraph( position, MT_VSModule );
        //position = addBackendIntoStrategyGraph( position, MT_CADModule );
		
		setStrategy({
			addBackend<PreprocessingModule<PreprocessingSettings1>>({
				addBackend<SATModule<SATSettings1>>({
					addBackend<ICPModule<ICPSettings1>>({
						addBackend<VSModule<VSSettings1>>({
							addBackend<CADModule<CADSettings1>>()
						})
					})
				})
			})
		});
    }

    RatTwo::~RatTwo(){}

}    // namespace smtrat
