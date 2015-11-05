/**
 * @file BESettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#pragma once

namespace smtrat
{
    struct BESettings1
    {
#ifdef __VS
		static const std::string getModuleName() { return "BEModule<BESettings1>"; }
#else
		static constexpr auto moduleName = "BEModule<BESettings1>";
#endif
        /**
         * Example for a setting.
         */
        static const bool example_setting = true;
    };
}
