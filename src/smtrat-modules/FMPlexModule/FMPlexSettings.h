#pragma once

namespace smtrat {
	struct FMPlexSettings1 {
		static constexpr auto moduleName = "FMPlexModule<FMPlexSettings1>";
		static constexpr auto constraintHeuristic = "Basic";
		static constexpr auto variableDirectionHeuristic = "Basic";
		static constexpr bool incremental = true;
	};

	struct FMPlexSettings2 {
		static constexpr auto moduleName = "FMPlexModule<FMPlexSettings2>";
		static constexpr auto constraintHeuristic = "Basic";
		static constexpr auto variableDirectionHeuristic = "Basic";
		static constexpr bool incremental = false;
	};
}