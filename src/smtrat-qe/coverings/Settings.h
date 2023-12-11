#pragma once

#include <smtrat-cadcells/representation/heuristics.h>
#include <smtrat-coveringng/FormulaEvaluationComplexity.h>
#include <smtrat-coveringng/VariableOrdering.h>
#include <smtrat-mcsat/variableordering/VariableOrdering.h>

namespace smtrat::qe::coverings {
struct DefaultSettings {
	// Variable ordering
	static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::GreedyMaxUnivariate;

	// Projection operator
	using op = cadcells::operators::MccallumComplete;
	static constexpr cadcells::representation::CellHeuristic cell_heuristic = cadcells::representation::BIGGEST_CELL;
	static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
	static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING;

	// Implicant computation
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::sotd, proj), 1, covering_ng::formula::complexity::min_tdeg, false, true, false, Type::PROPAGATION);
        }
    };
};
} // namespace smtrat::qe::coverings