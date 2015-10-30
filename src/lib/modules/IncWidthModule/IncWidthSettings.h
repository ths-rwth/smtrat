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
		static constexpr auto moduleName = "IncWidthModule<IncWidthSettings1>";
        /**
         * The increment of the width of the intervals specifying the variable domains.
         */
        static constexpr unsigned increment = 2;
        /**
         * The half of the starting width of the intervals specifying the variable domains. Starting interval domains are then: [-half_of_start_width,half_of_start_width]
         */
        static constexpr unsigned half_of_start_width = 2;
        /**
         * The half of the maximal width of the intervals specifying the variable domains.
         */
        static constexpr unsigned half_of_max_width = 0;
    };
}
