/**
 * @file BESettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#pragma once

#include "../../solver/ModuleSettings.h"

namespace smtrat
{
    struct BESettings1 : ModuleSettings
    {
		static constexpr auto moduleName = "BEModule<BESettings1>";
        /**
         * Example for a setting.
         */
        static const bool example_setting = true;
    };
}
