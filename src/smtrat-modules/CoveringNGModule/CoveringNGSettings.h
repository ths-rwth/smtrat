#pragma once
namespace smtrat {

struct CoveringNGSettingsDefault {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsDefault>";

    // Handling of Boolean variables
    static constexpr bool transform_boolean_variables_to_reals = true;

    // Variable ordering
    static constexpr mcsat::VariableOrdering variable_ordering = mcsat::VariableOrdering::GreedyMaxUnivariate;

    // Projection operator
    static constexpr cadcells::operators::op op = cadcells::operators::op::mccallum;
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING;
    static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING;

    // Implicant computation
    static constexpr auto formula_complexity_ordering = smtrat::covering_ng::formula::complexity::min_tdeg_ordering;
    static constexpr bool exhaustive_implicant_computation = false;
    static constexpr auto implicant_complexity_ordering = smtrat::covering_ng::formula::complexity::min_tdeg_min_size_implicant;
};

struct CoveringNGSettingsMinLvlMinTdeg : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsMinLvlMinTdeg>";

    static constexpr auto formula_complexity_ordering = smtrat::covering_ng::formula::complexity::min_lvl_min_tdeg_ordering;
};

struct CoveringNGSettingsExImplicants : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsExImplicants>";

    static constexpr bool exhaustive_implicant_computation = true;
    static constexpr auto implicant_complexity_ordering = smtrat::covering_ng::formula::complexity::min_tdeg_min_size_implicant;
};


} // namespace smtrat
