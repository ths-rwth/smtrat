/**
 * @file FPPSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

#include "../../solver/ModuleSettings.h"
#include "../../strategies/PreprocessingOne.h"
#include "../../strategies/BVPreprocessing.h"
#include "../../strategies/PBPreprocessing.h"

namespace smtrat
{
    struct FPPSettings1 : ModuleSettings
    {
		static constexpr auto moduleName = "FPPModule<FPPSettings1>";
        /**
         * The maximum number of iterations in order to reach a fix point during the repeated application of preprocessing.
         * If this number is negative, this procedure stops only if it indeed reached a fix point.
         */
        static const int max_iterations = 5;
        
        typedef PreprocessingOne Preprocessor;
    };
    
    struct FPPSettings2 : FPPSettings1
    {
		static constexpr auto moduleName = "FPPModule<FPPSettings2>";
        static const int max_iterations = -1;
    };

    struct FPPSettings3 : FPPSettings1
    {
	static constexpr auto moduleName = "FPPModule<FPPSettings3>";
	using Preprocessor = BVPreprocessing;
    };

    struct FPPSettingsPB : FPPSettings1
    {
	static constexpr auto moduleName = "FPPModule<FPPSettingsPB>";
	using Preprocessor = PBPreprocessing;
    };
}
