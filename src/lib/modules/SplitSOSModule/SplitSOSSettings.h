/**
 * @file SplitSOSSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

namespace smtrat
{
    struct SplitSOSSettings1
    {
#ifdef __VS
		static const std::string getModuleName() { return "SplitSOSModule<SplitSOSSettings1>"; }
#else
		static constexpr auto moduleName = "SplitSOSModule<SplitSOSSettings1>";
#endif
        /**
         * Example for a setting.
         */
        static const bool example_setting = true;
    };
}
