/**
 * @file FourierMotzkinSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2023-01-10
 * Created on 2023-01-10.
 */

#pragma once

namespace smtrat
{
	struct FourierMotzkinSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "FourierMotzkinModule<FourierMotzkinSettings1>";
		static constexpr bool incremental = false;
		static constexpr bool use_imbert = true;
		static constexpr fmplex::EQHandling eq_handling = fmplex::EQHandling::GAUSSIAN_TABLEAU;
		using gauss_type = fmplex::FMPlexGauss;
		static constexpr fmplex::NEQHandling neq_handling = fmplex::NEQHandling::SPLITTING_LEMMAS;
		static constexpr std::size_t nr_neq_splits_at_once = 1;
		static constexpr fmplex::StrictHandling strict_handling = fmplex::StrictHandling::DELTA_WEAKEN;
		static constexpr fmplex::ModelHeuristic model_heuristic = fmplex::ModelHeuristic::ON_BOUND;
	};
}
