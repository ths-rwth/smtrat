/**
 * @file NewCoveringSettings.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-07-08
 * Created on 2021-07-08.
 */

#pragma once

#include "Sampling.h"
#include <smtrat-cadcells/operators/operator.h>
#include <smtrat-cadcells/representation/heuristics.h>

#include <smtrat-mcsat/variableordering/VariableOrdering.h>

namespace smtrat {

struct NewCoveringSettings1 {
    static constexpr char moduleName[] = "NewCoveringModule<NewCovering>";
    static constexpr mcsat::VariableOrdering variableOrderingStrategy = mcsat::VariableOrdering::GreedyMaxUnivariate;
    static constexpr smtrat::cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING;
    static constexpr smtrat::cadcells::operators::op op = cadcells::operators::op::mccallum;
    static constexpr smtrat::SamplingAlgorithm sampling_algorithm = smtrat::SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING;
    static constexpr smtrat::IsSampleOutsideAlgorithm is_sample_outside_algorithm = smtrat::IsSampleOutsideAlgorithm::DEFAULT;
    static constexpr bool incremental = true;
    static constexpr bool backtracking = true;
};

struct NewCoveringSettings2 : NewCoveringSettings1 {
    static constexpr bool backtracking = false;
};

struct NewCoveringSettings3 : NewCoveringSettings1 {
    static constexpr bool incremental = false;
};

struct NewCoveringSettings4 : NewCoveringSettings1 {
    static constexpr bool incremental = false;
    static constexpr bool backtracking = false;
};

} // namespace smtrat
