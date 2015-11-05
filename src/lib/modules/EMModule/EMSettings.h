/**
 * @file EMSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

namespace smtrat
{
    struct EMSettings1
	{
#ifdef __VS
		static const std::string getModuleName() { return "EMModule<EMSettings1>"; }
#else
		static constexpr auto moduleName = "EMModule<EMSettings1>";
#endif
        /**
         * Example for a setting.
         */
        static const bool example_setting = true;
    };
}
