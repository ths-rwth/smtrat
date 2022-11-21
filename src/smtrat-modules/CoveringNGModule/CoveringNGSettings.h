#pragma once
namespace smtrat {

struct CoveringNGSettingsDefault {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsDefault>";
    static constexpr mcsat::VariableOrdering variable_ordering = mcsat::VariableOrdering::GreedyMaxUnivariate;
    static constexpr cadcells::operators::op op = cadcells::operators::op::mccallum;
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING;
    static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING;
    static constexpr auto formula_complexity_ordering = smtrat::covering_ng::formula::complexity::min_tdeg_ordering;
};

struct CoveringNGSettingsMinLvlMinTdeg : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsMinLvlMinTdeg>";
    static constexpr auto formula_complexity_ordering = smtrat::covering_ng::formula::complexity::min_lvl_min_tdeg_ordering;
};

} // namespace smtrat
