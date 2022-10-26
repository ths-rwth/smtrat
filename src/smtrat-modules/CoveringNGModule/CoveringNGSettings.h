#pragma once
namespace smtrat {

struct CoveringNGSettings1 {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettings1>";
    static constexpr mcsat::VariableOrdering variable_ordering = mcsat::VariableOrdering::GreedyMaxUnivariate;
    static constexpr cadcells::operators::op op = cadcells::operators::op::mccallum;
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING;
    static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING;
};

} // namespace smtrat
