/**
 * @file FMPlexSettings.h
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */

#pragma once

namespace smtrat {
	namespace fmplex {
		struct Base
		{
			static constexpr bool incremental = false;
			static constexpr EQHandling eq_handling = EQHandling::GAUSSIAN_TABLEAU;
			using gauss_type = FMPlexGauss;
			static constexpr NEQHandling neq_handling = NEQHandling::SPLITTING_LEMMAS;
			static constexpr std::size_t nr_neq_splits_at_once = 1;
			static constexpr StrictHandling strict_handling = StrictHandling::DELTA_WEAKEN;
			static constexpr ModelHeuristic model_heuristic = ModelHeuristic::ON_BOUND;
		};

		struct BT { static constexpr bool use_backtracking = true; };
		struct NoBT { static constexpr bool use_backtracking = false; };

		struct Prune { static constexpr bool ignore_pivots = true; };
		struct NoPrune { static constexpr bool ignore_pivots = false; };

		struct Optimized : BT, Prune {};
		struct NonOptimized : NoBT, NoPrune {};

		struct RandomVar { static constexpr VariableHeuristic variable_heuristic = VariableHeuristic::RANDOM; };
		struct FirstVar { static constexpr VariableHeuristic variable_heuristic = VariableHeuristic::COLUMN_ORDER; };
		struct BranchVar { static constexpr VariableHeuristic variable_heuristic = VariableHeuristic::LEAST_BRANCHES; };
		struct MinColVar { static constexpr VariableHeuristic variable_heuristic = VariableHeuristic::MIN_COL_LEN; };

		struct RandomElim 	{ static constexpr EliminatorHeuristic eliminator_heuristic = EliminatorHeuristic::RANDOM; };
		struct FirstElim 	{ static constexpr EliminatorHeuristic eliminator_heuristic = EliminatorHeuristic::ROW_ORDER; };
		struct LevelElim 	{ static constexpr EliminatorHeuristic eliminator_heuristic = EliminatorHeuristic::LOWEST_LEVEL; };
		struct MinRowElim 	{ static constexpr EliminatorHeuristic eliminator_heuristic = EliminatorHeuristic::MIN_ROW_LEN; };

		struct RandomHeur : RandomVar, RandomElim {};
		struct OrderedHeur : FirstVar, FirstElim {};
		struct OptHeur : BranchVar, LevelElim {};
		struct SimplexHeur : MinColVar, MinRowElim {};
	}
	
	// Settings names pattern: [] optional, () obligatory
	// FMPlexSettings[BT][Prune](Rand/First/Branch/MinCol)(Rand/First/Level/MinRow)

	// ------------------ No BT, No Prune ----------------------------------

	struct FMPlexSettingsRandRand : fmplex::Base, fmplex::NonOptimized, fmplex::RandomHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsRandRand>"; };

	struct FMPlexSettingsBranchLevel : fmplex::Base, fmplex::NonOptimized, fmplex::OptHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsBranchLevel>"; };

	struct FMPlexSettingsMinColMinRow : fmplex::Base, fmplex::NonOptimized, fmplex::SimplexHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsMinColMinRow>"; };

	// ------------------ BT, No Prune --------------------------------------

	struct FMPlexSettingsBTRandRand : fmplex::Base, fmplex::BT, fmplex::NoPrune, fmplex::RandomHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsBTRandRand>"; };

	struct FMPlexSettingsBTBranchLevel : fmplex::Base, fmplex::BT, fmplex::NoPrune, fmplex::OptHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsBTBranchLevel>"; };

	struct FMPlexSettingsBTMinColMinRow : fmplex::Base, fmplex::BT, fmplex::NoPrune, fmplex::SimplexHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsBTMinColMinRow>"; };

	// ------------------ No BT, Prune --------------------------------------

	struct FMPlexSettingsPruneRandRand : fmplex::Base, fmplex::NoBT, fmplex::Prune, fmplex::RandomHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsPruneRandRand>"; };

	struct FMPlexSettingsPruneBranchLevel : fmplex::Base, fmplex::NoBT, fmplex::Prune, fmplex::OptHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsPruneBranchLevel>"; };

	struct FMPlexSettingsPruneMinColMinRow : fmplex::Base, fmplex::NoBT, fmplex::Prune, fmplex::SimplexHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsPruneMinColMinRow>"; };

	// ------------------ BT, Prune -----------------------------------------

	struct FMPlexSettingsBTPruneRandRand : fmplex::Base, fmplex::Optimized, fmplex::RandomHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsBTPruneRandRand>"; };

	struct FMPlexSettingsBTPruneBranchLevel : fmplex::Base, fmplex::Optimized, fmplex::OptHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsBTPruneBranchLevel>"; };

	struct FMPlexSettingsBTPruneMinColMinRow : fmplex::Base, fmplex::Optimized, fmplex::SimplexHeur
	{ static constexpr auto moduleName = "FMPlexModule<FMPlexSettingsBTPruneMinColMinRow>"; };

} // namespace smtrat
