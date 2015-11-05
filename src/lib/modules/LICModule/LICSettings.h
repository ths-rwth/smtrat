/**
 * @file LICSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-03
 * Created on 2015-09-03.
 */

#pragma once

namespace smtrat
{
    struct LICSettings1
    {
#ifdef __VS
		static const std::string getModuleName() { return "LICModule<LICSettings1>"; }
#else
		static constexpr auto moduleName = "LICModule<LICSettings1>";
#endif
        /**
         * Example for a setting.
         */
        static const bool example_setting = true;
    };
}
