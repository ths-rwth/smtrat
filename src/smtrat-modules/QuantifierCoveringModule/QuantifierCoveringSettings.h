/**
 * @file QuantifierCoveringSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2023-04-17
 * Created on 2023-04-17.
 */

#pragma once

#include "smtrat-cadcells/representation/heuristics.h"
#include <smtrat-coveringng/FormulaEvaluationComplexity.h>
#include "smtrat-coveringng/VariableOrdering.h"

namespace smtrat
{

	struct QuantifierCoveringSettingsDefault
	{
		/// Name of the Module
		static constexpr auto moduleName = "QuantifierCoveringModule<QuantifierCoveringSettingsDefault>";

		static constexpr bool transform_boolean_variables_to_reals = true;

		static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::GreedyMaxUnivariate;

		using op = cadcells::operators::MccallumComplete;
		static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
		static constexpr cadcells::representation::CellHeuristic cell_heuristic = cadcells::representation::BIGGEST_CELL;
		static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING;
		
		struct formula_evaluation {
			using Type = covering_ng::formula::GraphEvaluation;
			static auto create(cadcells::datastructures::Projections& proj) {
				return Type(std::bind_front(covering_ng::formula::complexity::sotd, proj), 1, covering_ng::formula::complexity::min_tdeg, false, true, false, false);
			}
		};
	};

	struct base{

		static constexpr bool transform_boolean_variables_to_reals = true;

		/// Projection operator
		using op = cadcells::operators::Mccallum;
		static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING;
		static constexpr cadcells::representation::CellHeuristic cell_heuristic = cadcells::representation::BIGGEST_CELL;
		static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING;


		// Implicant computation
		struct formula_evaluation {
			using Type = covering_ng::formula::GraphEvaluation;
			static auto create(cadcells::datastructures::Projections& proj) {
				return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size_fact, proj), 1, covering_ng::formula::complexity::min_tdeg, false, true, false, false);
			}
		};
	};

	struct QuantifierCoveringSettingsLexicographic : base
	{
		/// Name of the Module
		static constexpr auto moduleName = "QuantifierCoveringModule<QuantifierCoveringSettingsLexicographic>";

		static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::FeatureBasedLexicographic;
	};	

	struct QuantifierCoveringSettingsBrown : base
	{
		/// Name of the Module
		static constexpr auto moduleName = "QuantifierCoveringModule<QuantifierCoveringSettingsBrown>";

		static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::FeatureBasedBrown;
	};

	struct QuantifierCoveringSettingsTriangular : base
	{
		/// Name of the Module
		static constexpr auto moduleName = "QuantifierCoveringModule<QuantifierCoveringSettingsTriangular>";

		static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::FeatureBasedTriangular;
	};

	struct QuantifierCoveringSettingsEarliestSplitting : base
	{
		/// Name of the Module
		static constexpr auto moduleName = "QuantifierCoveringModule<QuantifierCoveringSettingsEarliest>";

		static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::EarliestSplitting;
	};

}  // namespace smtrat