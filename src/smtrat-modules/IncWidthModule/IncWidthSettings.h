/**
 * @file IncWidthSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-06-29
 * Created on 2015-06-29.
 */


#pragma once

#include "../../solver/ModuleSettings.h"

namespace smtrat
{
    struct IncWidthSettings1 : ModuleSettings
    {
		static constexpr auto moduleName = "IncWidthModule<IncWidthSettings1>";
        /**
         * The increment of the width of the intervals specifying the variable domains.
         */
        static constexpr unsigned increment = 2;
        /**
         * The half of the starting width of the intervals specifying the variable domains. Starting interval domains are then: [-half_of_start_width,half_of_start_width]
         */
        static constexpr unsigned start_width = 1;
        /**
         * The half of the maximal width of the intervals specifying the variable domains.
         */
        static constexpr unsigned max_width = 4;
        /**
         * 
         */
        static constexpr bool exclude_searched_space = false;
        /**
         * 
         */
        static constexpr bool exclude_negative_numbers = true;
        /**
         * 
         */
        static constexpr bool use_icp = false;
    };
    
    struct IncWidthSettings2 : IncWidthSettings1
    {
        static constexpr auto moduleName = "IncWidthModule<IncWidthSettings2>";
        static constexpr unsigned max_width = 0;
    };
    
    struct IncWidthSettings3 : IncWidthSettings1
    {
        static constexpr auto moduleName = "IncWidthModule<IncWidthSettings3>";
        static constexpr bool exclude_searched_space = false;
    };
}
