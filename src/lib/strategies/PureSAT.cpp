/**
 * @file RatOne.cpp
 */

#include "PureSAT.h"
#include "../modules/Modules.h"

namespace smtrat
{

    PureSAT::PureSAT( bool _externalModuleFactoryAdding ):
        Manager( _externalModuleFactoryAdding )
    {
		setStrategy({
			addBackend<SATModule<SATSettings1>>()
		});
    }

    PureSAT::~PureSAT(){}

}    // namespace smtrat
