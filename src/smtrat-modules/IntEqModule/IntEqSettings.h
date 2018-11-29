/**
 * @file IntEqSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-11-24
 * Created on 2014-11-24.
 */


#pragma once

#include "../ModuleSettings.h"

namespace smtrat
{
    struct IntEqSettings1 : ModuleSettings
    {
		static constexpr auto moduleName = "IntEqModule<IntEqSettings1>";
        /**
         * Example for a setting.
         */
        static const bool example_setting = true;
    };
}
