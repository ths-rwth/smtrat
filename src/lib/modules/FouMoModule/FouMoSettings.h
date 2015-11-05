/**
 * @file FouMoSettings.h
 * @author Dustin Huetter <dustin.huetter@rwth-aachen.de>
 *
 * @version 2014-12-01
 * Created on 2014-12-01.
 */


#pragma once

namespace smtrat
{
    struct FouMoSettings1
    {
#ifdef __VS
		static const std::string getModuleName() { return "FouMoModule<FouMoSettings1>"; }
#else
		static constexpr auto moduleName = "FouMoModule<FouMoSettings1>";
#endif
        static const bool Allow_Deletion = true;       
        // The threshold, in percentage, for determining whether to run the backends
        static const unsigned Threshold = 50;        
    };
}
