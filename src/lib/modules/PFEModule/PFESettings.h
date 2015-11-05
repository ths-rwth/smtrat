/**
 * @file PFESettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

namespace smtrat
{
    struct PFESettings1
	{
#ifdef __VS
		static const std::string getModuleName() { return "PFEModule<PFESettings1>"; }
#else
		static constexpr auto moduleName = "PFEModule<PFESettings1>";
#endif
        /**
         * Example for a setting.
         */
        static const bool example_setting = true;
    };
}
