#pragma once

#include <smtrat-coveringng/FormulaEvaluation.h>
#include <smtrat-coveringng/FormulaEvaluationGraph.h>
#include <smtrat-coveringng/FormulaEvaluationNode.h>
#include <smtrat-coveringng/FormulaEvaluationComplexity.h>
#include <smtrat-coveringng/VariableOrdering.h>
#include <smtrat-coveringng/Sampling.h>
#include <smtrat-cadcells/operators/operator.h>
#include <smtrat-cadcells/representation/heuristics.h>

namespace smtrat {

struct CoveringNGSettingsDefault {
    static constexpr char moduleName[] = "CoveringNGModule<CoveringNGSettingsDefault>";

    // Handling of Boolean variables
    static constexpr bool transform_boolean_variables_to_reals = true;

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
            auto fe_implicant_ordering = covering_ng::formula::complexity::sotd;
            std::size_t fe_results = 1;
            auto fe_constraint_ordering = covering_ng::formula::complexity::min_tdeg;
            bool fe_stop_evaluation_on_conflict = false;
            bool fe_preprocess = true;
            bool fe_postprocess = false;
            auto fe_boolean_exploration = covering_ng::formula::GraphEvaluation::PROPAGATION;
            return Type(std::bind_front(fe_implicant_ordering, proj), fe_results, fe_constraint_ordering, fe_stop_evaluation_on_conflict, fe_preprocess, fe_postprocess, fe_boolean_exploration);
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


} // namespace smtrat
