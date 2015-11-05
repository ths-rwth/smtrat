/**
 * @file CBSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

namespace smtrat
{
    struct CBSettings1
    {
#ifdef __VS
		static const std::string getModuleName() { return "CBModule<CBSettings1>"; }
#else
		static constexpr auto moduleName = "CBModule<CBSettings1>";
#endif
        /**
         * Example for a setting.
         */
        static const bool example_setting = true;
    };
}
