#pragma once

namespace smtrat {
	struct FMPlexSettings1 {
		static constexpr auto moduleName = "FMPlexModule<FMPlexSettings1>";
		static constexpr auto constraintHeuristic = "Simple";
		static constexpr auto variableDirectionHeuristic = "Simple";
		static constexpr bool incremental = true;
		static constexpr auto backtrackingMode = "furthest";
	};

	struct FMPlexSettings2 {
		static constexpr auto moduleName = "FMPlexModule<FMPlexSettings2>";
		static constexpr auto constraintHeuristic = "Simple";
		static constexpr auto variableDirectionHeuristic = "Simple";
		static constexpr bool incremental = false;
		static constexpr auto backtrackingMode = "furthest";
	};

	struct FMPlexSettings3 {
		static constexpr auto moduleName = "FMPlexModule<FMPlexSettings3>";
		static constexpr auto constraintHeuristic = "Simple";
		static constexpr auto variableDirectionHeuristic = "Simple";
		static constexpr bool incremental = true;
		static constexpr auto backtrackingMode = "oneStep";
	};

	struct FMPlexSettings4 {
		static constexpr auto moduleName = "FMPlexModule<FMPlexSettings4>";
		static constexpr auto constraintHeuristic = "Simple";
		static constexpr auto variableDirectionHeuristic = "Simple";
		static constexpr bool incremental = false;
		static constexpr auto backtrackingMode = "oneStep";
	};
}