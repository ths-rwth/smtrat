/**
 * @file IncWidthSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-06-29
 * Created on 2015-06-29.
 */


#pragma once

namespace smtrat
{
    struct IncWidthSettings1
    {
#ifdef __VS
		static const std::string getModuleName() { return "IncWidthModule<IncWidthSettings1>"; }
#else
		static constexpr auto moduleName = "IncWidthModule<IncWidthSettings1>";
#endif
        /**
         * The increment of the width of the intervals specifying the variable domains.
         */
        static CONSTEXPR unsigned increment = 2;
        /**
         * The half of the starting width of the intervals specifying the variable domains. Starting interval domains are then: [-half_of_start_width,half_of_start_width]
         */
		static CONSTEXPR unsigned half_of_start_width = 1;
        /**
         * The half of the maximal width of the intervals specifying the variable domains.
         */
		static CONSTEXPR unsigned half_of_max_width = 8;
    };
    
    struct IncWidthSettings2 : IncWidthSettings1
    {
#ifdef __VS
		static const std::string getModuleName() { return "IncWidthModule<IncWidthSettings2>"; }
#else
		static constexpr auto moduleName = "IncWidthModule<IncWidthSettings2>";
#endif
		static CONSTEXPR unsigned half_of_max_width = 0;
    };
}
