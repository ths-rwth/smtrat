/**
 * @file RatICP.cpp
 */

#include "RatICP.h"
#include "../modules/Modules.h"

namespace smtrat
{

    RatICP::RatICP( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
		setStrategy({
			addBackend<PreprocessingModule<PreprocessingSettings1>>({
				addBackend<SATModule<SATSettings1>>({
					addBackend<ICPModule<ICPSettings1>>()
				})
			})
		});
    }

    RatICP::~RatICP(){}

}    // namespace smtrat
