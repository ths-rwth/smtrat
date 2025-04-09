#pragma once

#include <smtrat-solver/Manager.h>


#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-cadcells/operators/operator_mccallum_unified.h>
#include <smtrat-coveringng/FormulaEvaluationNoop.h>


namespace smtrat {

namespace internal {
struct CoveringNGSettings : CoveringNGSettingsDefault  {
	using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
	using covering_heuristic = cadcells::representation::covering_heuristics::FullCovering;
	using op = cadcells::operators::MccallumUnified<cadcells::operators::MccallumUnifiedSettingsComplete>;
	static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::FeatureBasedPickering;
	static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::SIZE_SAMPLING;
	static constexpr bool move_boolean_variables_to_front = true;

	struct formula_evaluation {
        using Type = covering_ng::formula::NoopEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            auto fe_constraint_ordering = covering_ng::formula::complexity::min_tdeg;
            return Type(proj, fe_constraint_ordering);
        }
    };
};
}

class Eval_CalcNoopFull : public Manager {
public:
	Eval_CalcNoopFull() : Manager() {
		setStrategy(
			
                addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
            
        );
	}
};

} // namespace smtrat
