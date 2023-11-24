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
        static auto create(cadcells::datastructures::Projections&) {
            return Type(covering_ng::formula::node_ds::complexity::min_tdeg_ordering);
        }
    };
};

struct CoveringNGSettingsMinLvlMinTdeg : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsMinLvlMinTdeg>";

    struct formula_evaluation {
        using Type = covering_ng::formula::Minimal;
        static auto create(cadcells::datastructures::Projections&) {
            return Type(covering_ng::formula::node_ds::complexity::min_lvl_min_tdeg_ordering);
        }
    };
};

struct CoveringNGSettingsExImplicants : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsExImplicants>";
    struct formula_evaluation {
        using Type = covering_ng::formula::ExhaustiveImplicants;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size, proj), 1);
        }
    };
};

struct CoveringNGSettingsExImplicantsMulti : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsExImplicantsMulti>";
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
    struct formula_evaluation {
        using Type = covering_ng::formula::ExhaustiveImplicants;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size, proj), 0);
        }
    };
};

struct CoveringNGSettingsExImplicantsMinSize : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsExImplicantsMinSize>";
    struct formula_evaluation {
        using Type = covering_ng::formula::ExhaustiveImplicants;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_size_min_tdeg, proj), 1);
        }
    };
};

struct CoveringNGSettingsExImplicantsPruning : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsExImplicantsPruning>";
    struct formula_evaluation {
        using Type = covering_ng::formula::ExhaustiveImplicants;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size, proj), 1, 2);
        }
    };
};

struct CoveringNGSettingsGraphMulti : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsGraphMulti>";
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size, proj), 0, covering_ng::formula::complexity::min_tdeg, false, true, false, false);
        }
    };
};

struct CoveringNGSettingsGraphSingle : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsGraphSingle>";
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size, proj), 1, covering_ng::formula::complexity::min_tdeg, true, true, false, false);
        }
    };
};

struct CoveringNGSettingsGraphTwo : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsGraphTwo>";
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size, proj), 2, covering_ng::formula::complexity::min_tdeg, false, true, false, false);
        }
    };
};

struct CoveringNGSettingsGraphSingleChoice : CoveringNGSettingsDefault  {// currently the best!
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsGraphSingleChoice>";
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size, proj), 1, covering_ng::formula::complexity::min_tdeg, false, true, false, false);
        }
    };
};

struct CoveringNGSettingsGraphSingleChoiceLDB : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsGraphSingleChoiceLDB>";
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::LDB_COVERING;
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size, proj), 1, covering_ng::formula::complexity::min_tdeg, false, true, false, false);
        }
    };
};

struct CoveringNGSettingsGraphSingleChoiceFullBoolean : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsGraphSingleChoiceFullBoolean>";
    static constexpr bool transform_boolean_variables_to_reals = false;
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size, proj), 1, covering_ng::formula::complexity::min_tdeg, false, true, false, true, true);
        }
    };
};

struct CoveringNGSettingsGraphSingleChoicePostprocess : CoveringNGSettingsDefault  { 
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsGraphSingleChoice>";
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size, proj), 1, covering_ng::formula::complexity::min_tdeg, false, true, true, false);
        }
    };
};

struct CoveringNGSettingsGraphSingleChoicePickering : CoveringNGSettingsGraphSingleChoice {
    static constexpr mcsat::VariableOrdering variable_ordering = mcsat::VariableOrdering::FeatureBasedPickering;
};

struct CoveringNGSettingsGraphSingleChoiceBrown : CoveringNGSettingsGraphSingleChoice {
    static constexpr mcsat::VariableOrdering variable_ordering = mcsat::VariableOrdering::FeatureBasedBrown;
};

struct CoveringNGSettingsGraphSingleChoiceFact : CoveringNGSettingsDefault  {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsGraphSingleChoiceStdeg>";
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::min_max_tdeg_min_size_fact, proj), 1, covering_ng::formula::complexity::min_tdeg, false, true, false, false);
        }
    };
};

} // namespace smtrat
