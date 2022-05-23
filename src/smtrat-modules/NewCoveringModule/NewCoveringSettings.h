/**
 * @file NewCoveringSettings.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-07-08
 * Created on 2021-07-08.
 */

#pragma once

#include <smtrat-cadcells/operators/operator.h>
#include <smtrat-cadcells/representation/heuristics.h>
#include "Sampling.h"

#include <smtrat-mcsat/variableordering/VariableOrdering.h>

namespace smtrat
{
	struct NewCoveringSettings1
	{
		/// Name of the Module
		static constexpr char moduleName[] = "NewCoveringModule<NewCoveringSettings1>";
		static constexpr mcsat::VariableOrdering variableOrderingStrategy = mcsat::VariableOrdering::GreedyMaxUnivariate;
		static constexpr smtrat::cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::DEFAULT_COVERING;
		static constexpr smtrat::cadcells::operators::op op = cadcells::operators::op::mccallum;
		static constexpr smtrat::SamplingAlgorithm sampling_algorithm = smtrat::SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING_WITH_BOUNDS;
		static constexpr smtrat::IsSampleOutsideAlgorithm is_sample_outside_algorithm = smtrat::IsSampleOutsideAlgorithm::BOUND_FOCUS;
	};
}
