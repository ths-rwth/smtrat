#pragma once

namespace smtrat::fmplex {
    enum class EQHandling {
		GAUSSIAN_TABLEAU,
		GAUSSIAN_EIGEN,
		SPLITTING
	};

	enum class NEQHandling {
		MULTI_MODEL,
		SPLITTING_LEMMAS
	};

	enum class StrictHandling {
		DELTA_WEAKEN,
		FM_COMBINE
	};

	enum class VariableHeuristic {
		COLUMN_ORDER,
		LEAST_BRANCHES
	};

	enum class EliminatorHeuristic {
		ROW_ORDER,
		LOWEST_LEVEL
	};
} // namespace smtrat::fmplex