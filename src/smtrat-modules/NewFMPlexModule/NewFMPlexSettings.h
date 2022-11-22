/**
 * @file NewFMPlexSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */

#pragma once

namespace smtrat {
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

	// TODO: strict handling (delta or FM)

	struct NewFMPlexSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettings1>";

		static constexpr bool incremental = false;
		static constexpr bool use_backtracking = false;
		static constexpr bool ignore_pivots = false;
		static constexpr EQHandling eq_handling = EQHandling::GAUSSIAN_TABLEAU;
		static constexpr NEQHandling neq_handling = NEQHandling::SPLITTING_LEMMAS;
		static constexpr std::size_t nr_neq_splits_at_once = 2;
		static constexpr StrictHandling strict_handling = StrictHandling::FM_COMBINE;
		static constexpr VariableHeuristic variable_heuristic = VariableHeuristic::COLUMN_ORDER;
		static constexpr EliminatorHeuristic eliminator_heuristic = EliminatorHeuristic::ROW_ORDER;
	};
} // namespace smtrat
