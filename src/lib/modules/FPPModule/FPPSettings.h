/**
 * @file FPPSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once
#include "../../strategies/strategies.h"

namespace smtrat
{
    struct FPPSettings1
    {
        /**
         * The maximum number of iterations in order to reach a fix point during the repeated application of preprocessing.
         * If this number is negative, this procedure stops only if it indeed reached a fix point.
         */
        static const int max_iterations = 1;
        
        typedef PreprocessingOne Preprocessor;
    };
}
