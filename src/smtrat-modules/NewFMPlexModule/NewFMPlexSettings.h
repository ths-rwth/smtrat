/**
 * @file NewFMPlexSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
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
	// NewFMPlexSettings[BT][Prune](Rand/First/Branch/MinCol)(Rand/First/Level/MinRow)

	// ------------------ No BT, No Prune ----------------------------------

	struct NewFMPlexSettingsRandRand : fmplex::Base, fmplex::NonOptimized, fmplex::RandomHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsRandRand>"; };

	struct NewFMPlexSettingsBranchLevel : fmplex::Base, fmplex::NonOptimized, fmplex::OptHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsBranchLevel>"; };

	struct NewFMPlexSettingsMinColMinRow : fmplex::Base, fmplex::NonOptimized, fmplex::SimplexHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsMinColMinRow>"; };

	// ------------------ BT, No Prune --------------------------------------

	struct NewFMPlexSettingsBTRandRand : fmplex::Base, fmplex::BT, fmplex::NoPrune, fmplex::RandomHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsBTRandRand>"; };

	struct NewFMPlexSettingsBTBranchLevel : fmplex::Base, fmplex::BT, fmplex::NoPrune, fmplex::OptHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsBTBranchLevel>"; };

	struct NewFMPlexSettingsBTMinColMinRow : fmplex::Base, fmplex::BT, fmplex::NoPrune, fmplex::SimplexHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsBTMinColMinRow>"; };

	// ------------------ No BT, Prune --------------------------------------

	struct NewFMPlexSettingsPruneRandRand : fmplex::Base, fmplex::NoBT, fmplex::Prune, fmplex::RandomHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsPruneRandRand>"; };

	struct NewFMPlexSettingsPruneBranchLevel : fmplex::Base, fmplex::NoBT, fmplex::Prune, fmplex::OptHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsPruneBranchLevel>"; };

	struct NewFMPlexSettingsPruneMinColMinRow : fmplex::Base, fmplex::NoBT, fmplex::Prune, fmplex::SimplexHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsPruneMinColMinRow>"; };

	// ------------------ BT, Prune -----------------------------------------

	struct NewFMPlexSettingsBTPruneRandRand : fmplex::Base, fmplex::Optimized, fmplex::RandomHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsBTPruneRandRand>"; };

	struct NewFMPlexSettingsBTPruneBranchLevel : fmplex::Base, fmplex::Optimized, fmplex::OptHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsBTPruneBranchLevel>"; };

	struct NewFMPlexSettingsBTPruneMinColMinRow : fmplex::Base, fmplex::Optimized, fmplex::SimplexHeur
	{ static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsBTPruneMinColMinRow>"; };

} // namespace smtrat
