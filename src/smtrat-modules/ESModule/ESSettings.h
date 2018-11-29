/**
 * @file ESSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#pragma once

#include "../ModuleSettings.h"

namespace smtrat
{
    struct ESSettings1 : ModuleSettings
    {
		static constexpr auto moduleName = "ESModule<ESSettings1>";
        /**
         * Example for a setting.
         */
        static const bool example_setting = true;
    };
}
