/**
 * @file FouMoSettings.h
 * @author Dustin Huetter <dustin.huetter@rwth-aachen.de>
 *
 * @version 2014-12-01
 * Created on 2014-12-01.
 */


#pragma once

#include "../ModuleSettings.h"

namespace smtrat
{
    struct FouMoSettings1 : ModuleSettings
    {        
		static constexpr auto moduleName = "FouMoModule<FouMoSettings1>";
        static const bool Allow_Deletion = true;       
        // The threshold, in percentage, for determining whether to run the backends
        static const unsigned Threshold = 50;        
    };
}
