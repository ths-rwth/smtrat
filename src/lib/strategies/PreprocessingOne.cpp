/**
 * @file PreprocessingOne.cpp
 */

#include "PreprocessingOne.h"
#include "../modules/Modules.h"

namespace smtrat
{
    
    PreprocessingOne::PreprocessingOne( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
        //size_t position = 0;
        //position = addBackendIntoStrategyGraph( position, MT_EMModule );
        //position = addBackendIntoStrategyGraph( position, MT_RPFModule );
        //position = addBackendIntoStrategyGraph( position, MT_SplitSOSModule );
        //position = addBackendIntoStrategyGraph( position, MT_ESModule );
        //position = addBackendIntoStrategyGraph( position, MT_BEModule );
        //position = addBackendIntoStrategyGraph( position, MT_CBModule );
		
		setStrategy({
			addBackend<EMModule<EMSettings1>>({
				addBackend<RPFModule<RPFSettings1>>({
					addBackend<SplitSOSModule<SplitSOSSettings1>>({
						addBackend<ESModule<ESSettings1>>({
							addBackend<BEModule<BESettings1>>(
								addBackend<CBModule<CBSettings1>>()
							)
						})
					})
				})
			})
		});
    }

    PreprocessingOne::~PreprocessingOne(){}

}    // namespace smtrat
