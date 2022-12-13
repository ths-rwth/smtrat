/**
 * @file NewFMPlexSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */

#pragma once

namespace smtrat {
	struct NewFMPlexBaseSettings
	{
		static constexpr bool incremental = false;
		static constexpr fmplex::EQHandling eq_handling = fmplex::EQHandling::GAUSSIAN_TABLEAU;
		using gauss_type = fmplex::FMPlexGauss;
		static constexpr fmplex::NEQHandling neq_handling = fmplex::NEQHandling::SPLITTING_LEMMAS;
		static constexpr std::size_t nr_neq_splits_at_once = 1;
		static constexpr fmplex::StrictHandling strict_handling = fmplex::StrictHandling::DELTA_WEAKEN;
		static constexpr fmplex::EliminatorHeuristic eliminator_heuristic = fmplex::EliminatorHeuristic::ROW_ORDER;
	};

	struct NewFMPlexSettingsSimple : NewFMPlexBaseSettings
	{
		static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsSimple>";
		static constexpr bool use_backtracking = false;
		static constexpr bool ignore_pivots = false;
		static constexpr fmplex::VariableHeuristic variable_heuristic = fmplex::VariableHeuristic::COLUMN_ORDER;
	};

	struct NewFMPlexSettingsOnlyBt : NewFMPlexBaseSettings
	{
		static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsOnlyBt>";
		static constexpr bool use_backtracking = true;
		static constexpr bool ignore_pivots = false;
		static constexpr fmplex::VariableHeuristic variable_heuristic = fmplex::VariableHeuristic::COLUMN_ORDER;
	};

	struct NewFMPlexSettingsOnlyPrune : NewFMPlexBaseSettings
	{
		static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsOnlyPrune>";
		static constexpr bool use_backtracking = false;
		static constexpr bool ignore_pivots = true;
		static constexpr fmplex::VariableHeuristic variable_heuristic = fmplex::VariableHeuristic::COLUMN_ORDER;
	};

	struct NewFMPlexSettingsOnlyHeur : NewFMPlexBaseSettings
	{
		static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsOnlyHeur>";
		static constexpr bool use_backtracking = false;
		static constexpr bool ignore_pivots = false;
		static constexpr fmplex::VariableHeuristic variable_heuristic = fmplex::VariableHeuristic::LEAST_BRANCHES;
	};

	struct NewFMPlexSettingsBtPruneHeur : NewFMPlexBaseSettings
	{
		static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettingsBtPruneHeur>";
		static constexpr bool use_backtracking = true;
		static constexpr bool ignore_pivots = true;
		static constexpr fmplex::VariableHeuristic variable_heuristic = fmplex::VariableHeuristic::LEAST_BRANCHES;
	};
} // namespace smtrat
