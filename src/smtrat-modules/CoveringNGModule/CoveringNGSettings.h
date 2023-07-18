#pragma once

#include <smtrat-coveringng/FormulaEvaluationComplexity.h>

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
    struct formula_evaluation {
        using Type = covering_ng::formula::Minimal;
        static auto create() {
            return Type(covering_ng::formula::node_ds::complexity::min_tdeg_ordering);
        }
    };
};

struct CoveringNGSettingsMinLvlMinTdeg : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsMinLvlMinTdeg>";

    struct formula_evaluation {
        using Type = covering_ng::formula::Minimal;
        static auto create() {
            return Type(covering_ng::formula::node_ds::complexity::min_lvl_min_tdeg_ordering);
        }
    };
};

struct CoveringNGSettingsExImplicants : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsExImplicants>";
    struct formula_evaluation {
        using Type = covering_ng::formula::ExhaustiveImplicants;
        static auto create() {
            return Type(covering_ng::formula::node_ds::complexity::min_tdeg_min_size_implicant, 1);
        }
    };
};

struct CoveringNGSettingsExImplicantsMulti : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsExImplicantsMulti>";
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
    struct formula_evaluation {
        using Type = covering_ng::formula::ExhaustiveImplicants;
        static auto create() {
            return Type(covering_ng::formula::node_ds::complexity::min_tdeg_min_size_implicant, 0);
        }
    };
};

struct CoveringNGSettingsExImplicantsMinSize : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsExImplicantsMinSize>";
    struct formula_evaluation {
        using Type = covering_ng::formula::ExhaustiveImplicants;
        static auto create() {
            return Type(covering_ng::formula::node_ds::complexity::min_size_min_tdeg_implicant, 1);
        }
    };
};

struct CoveringNGSettingsExImplicantsPruning : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsExImplicantsPruning>";
    struct formula_evaluation {
        using Type = covering_ng::formula::ExhaustiveImplicants;
        static auto create() {
            return Type(covering_ng::formula::node_ds::complexity::min_tdeg_min_size_implicant, 1, 2);
        }
    };
};

struct CoveringNGSettingsGraph : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsGraph>";
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create() {
            return Type();
        }
    };
};


} // namespace smtrat
