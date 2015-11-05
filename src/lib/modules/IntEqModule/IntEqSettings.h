/**
 * @file IntEqSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-11-24
 * Created on 2014-11-24.
 */


#pragma once

namespace smtrat
{
    struct IntEqSettings1
    {
#ifdef __VS
		static const std::string getModuleName() { return "IntEqModule<IntEqSettings1>"; }
#else
		static constexpr auto moduleName = "IntEqModule<IntEqSettings1>";
#endif
        /**
         * Example for a setting.
         */
        static const bool example_setting = true;
    };
}
