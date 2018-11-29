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

#include "../ModuleSettings.h"

namespace smtrat
{
	enum class MISHeuristic {
		TRIVIAL, GREEDY
	};
	
	enum class SplitHeuristic {
		FIRST, LAST
	};

	struct CADSettingsReal : ModuleSettings
	{
		static constexpr auto moduleName = "CADModule<CADSettingsReal>";
		static constexpr carl::cad::IntegerHandling integerHandling = carl::cad::IntegerHandling::NONE;
		static constexpr SplitHeuristic splitHeuristic = SplitHeuristic::FIRST;
		static constexpr bool ignoreRoots = false;

		static constexpr MISHeuristic mis_heuristic = MISHeuristic::GREEDY;
		static constexpr bool computeConflictGraph = (mis_heuristic != MISHeuristic::TRIVIAL);
		static constexpr bool checkMISForMinimality = false;

		static const bool dummy;
	};

	struct CADSettingsSplitFirst : CADSettingsReal
	{
		static constexpr auto moduleName = "CADModule<SplitFirst>";
		static constexpr carl::cad::IntegerHandling integerHandling = carl::cad::IntegerHandling::SPLIT_ASSIGNMENT;
		static constexpr SplitHeuristic splitHeuristic = SplitHeuristic::FIRST;
	};
	struct CADSettingsSplitLast : CADSettingsReal
	{
		static constexpr auto moduleName = "CADModule<SplitFirst>";
		static constexpr carl::cad::IntegerHandling integerHandling = carl::cad::IntegerHandling::SPLIT_ASSIGNMENT;
		static constexpr SplitHeuristic splitHeuristic = SplitHeuristic::LAST;
	};
	struct CADSettingsSplitPath : CADSettingsReal
	{
		static constexpr auto moduleName = "CADModule<SplitPath>";
		static constexpr carl::cad::IntegerHandling integerHandling = carl::cad::IntegerHandling::SPLIT_PATH;
	};
	struct CADSettingsNoRoots : CADSettingsReal
	{
		static constexpr auto moduleName = "CADModule<NoRoots>";
		static constexpr carl::cad::IntegerHandling integerHandling = carl::cad::IntegerHandling::SPLIT_ASSIGNMENT;
		static constexpr SplitHeuristic splitHeuristic = SplitHeuristic::FIRST;
		static constexpr bool ignoreRoots = true;
	};
}
