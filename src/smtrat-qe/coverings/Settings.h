#pragma once

#include <smtrat-cadcells/representation/heuristics.h>
#include <smtrat-coveringng/FormulaEvaluationComplexity.h>
#include <smtrat-coveringng/VariableOrdering.h>
#include <smtrat-mcsat/variableordering/VariableOrdering.h>
#include <smtrat-cadcells/operators/operator_mccallum_pdel.h>
#include <smtrat-cadcells/operators/operator_mccallum_unified.h>

namespace smtrat::qe::coverings {
struct BaseSettings {
	// Variable ordering
    static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::GreedyMaxUnivariate;

    // Projection operator
    using op = cadcells::operators::Mccallum<cadcells::operators::MccallumSettingsComplete>;
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCell;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringMinTdeg;
    static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::LOWER_UPPER_BETWEEN_SAMPLING_AVOID_RAN;

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
            return Type(proj, fe_implicant_ordering, fe_results, fe_constraint_ordering, fe_stop_evaluation_on_conflict, fe_preprocess, fe_postprocess, fe_boolean_exploration);
        }
    };

    static constexpr bool transform_boolean_variables_to_reals = true;
    static constexpr bool move_boolean_variables_to_back = false;
    static constexpr bool move_boolean_variables_to_front = false;
};

struct DefaultBCFilterSettings : BaseSettings {
    struct mcf_settings : cadcells::operators::MccallumFilteredSettings {
        static constexpr DelineationFunction delineation_function = NOOP;
        static constexpr bool complete = true;
    };
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
    using op = cadcells::operators::MccallumFiltered<mcf_settings>;
};



struct DefaultBCFilterEWSettings : BaseSettings {
    struct mcf_settings : cadcells::operators::MccallumFilteredSettings {
        static constexpr DelineationFunction delineation_function = BOUNDS_ONLY;
        static constexpr bool enable_weak = true;
        static constexpr bool complete = true;
    };
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
    using op = cadcells::operators::MccallumFiltered<mcf_settings>;
    static constexpr bool enable_weak = true;
};


struct DefaultBCSettings : BaseSettings {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCell;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCovering;
    using op = cadcells::operators::Mccallum<cadcells::operators::MccallumSettingsComplete>;
};


struct DefaultBCpdelSettings : BaseSettings {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellPdel;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringPdel;
    using op = cadcells::operators::MccallumPdel<cadcells::operators::MccallumPdelSettingsComplete>;
};

struct EvalSettings : BaseSettings {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
	using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
	using op = cadcells::operators::MccallumUnified<cadcells::operators::MccallumUnifiedSettingsComplete>;
	static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::FeatureBasedPickering;
	static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::SIZE_SAMPLING;
	static constexpr bool move_boolean_variables_to_front = true;
};

struct EvalPBcldboundsSettings : EvalSettings {
    struct OpSettings : cadcells::operators::MccallumUnifiedSettingsComplete {
		static constexpr DelineationFunction delineation_function = BOUNDS_ONLY;
		static constexpr bool enable_weak = true;
	};
	using op = cadcells::operators::MccallumUnified<OpSettings>;
};


struct DefaultSettings : BaseSettings {
    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
	using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
	static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::FeatureBasedPickering;
	static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::SIZE_SAMPLING;
	static constexpr bool move_boolean_variables_to_front = true;
    struct OpSettings : cadcells::operators::MccallumFilteredCompleteSettings {
		static constexpr DelineationFunction delineation_function = BOUNDS_ONLY;
		static constexpr bool enable_weak = true;
	};
	using op = cadcells::operators::MccallumFiltered<OpSettings>;
};


} // namespace smtrat::qe::coverings