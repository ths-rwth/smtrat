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

#include "../../solver/ModuleSettings.h"

#include "../../utilities/SettingsManager.h"

namespace smtrat
{
	enum class MISHeuristic {
		TRIVIAL, GREEDY
	};

	struct CADSettingsReal : ModuleSettings
	{
		static constexpr auto moduleName = "CADModule<CADSettingsReal>";
		static constexpr carl::cad::IntegerHandling integerHandling = carl::cad::IntegerHandling::NONE;

		static constexpr MISHeuristic mis_heuristic = MISHeuristic::GREEDY;
		static constexpr bool computeConflictGraph = (mis_heuristic != MISHeuristic::TRIVIAL);
		static constexpr bool checkMISForMinimality = false;

		static const bool dummy;
	};

	struct CADSettingsSplitAssignment : CADSettingsReal
	{
		static constexpr auto moduleName = "CADModule<SplitAssignment>";
		static constexpr carl::cad::IntegerHandling integerHandling = carl::cad::IntegerHandling::SPLIT_ASSIGNMENT;
	};
	struct CADSettingsSplitPath : CADSettingsReal
	{
		static constexpr auto moduleName = "CADModule<SplitPath>";
		static constexpr carl::cad::IntegerHandling integerHandling = carl::cad::IntegerHandling::SPLIT_PATH;
	};
}
