/**
 * @file CADSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

#include <iostream>

#include <carl/cad/CADSettings.h>

#include "../../utilities/SettingsManager.h"

namespace smtrat
{    
	enum class MISHeuristic {
		TRIVIAL, GREEDY
	};
    
    struct CADSettings1
    {
#ifdef __VS
	#define CONSTEXPR const
	static const std::string moduleName;
#else
	#define CONSTEXPR constexpr
	static CONSTEXPR auto moduleName = "CADModule<CADSettings1>";
#endif

		static CONSTEXPR carl::cad::IntegerHandling integerHandling = carl::cad::IntegerHandling::SPLIT_EARLY;
        
		static CONSTEXPR MISHeuristic mis_heuristic = MISHeuristic::GREEDY;
		static CONSTEXPR bool computeConflictGraph = (mis_heuristic != MISHeuristic::TRIVIAL);
		static CONSTEXPR bool checkMISForMinimality = false;
        
        static const bool dummy;
    };

#ifdef __VS
	const std::string CADSettings1::moduleName = "CADModule<CADSettings1>";
#endif
}
