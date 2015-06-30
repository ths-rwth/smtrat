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
        /**
         * The increment of the width of the intervals specifying the variable domains.
         */
        static const Rational increment = Rational(2);
        /**
         * The half of the starting width of the intervals specifying the variable domains. Starting interval domains are then: [-half_of_start_width,half_of_start_width]
         */
        static const Rational half_of_start_width = Rational(2);
    };
}
