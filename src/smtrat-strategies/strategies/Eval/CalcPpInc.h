#pragma once

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.tpp>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-solver/Manager.h>
#include <smtrat-cadcells/operators/operator_mccallum_unified.h>

namespace smtrat {

namespace internal {
struct NewCoveringSettings : NewCoveringSettings2 {
	using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
	using op = cadcells::operators::MccallumUnified<cadcells::operators::MccallumUnifiedSettingsComplete>;
	static constexpr mcsat::VariableOrdering variableOrderingStrategy = mcsat::VariableOrdering::GreedyMaxUnivariate;
	static constexpr covering_ng::SamplingAlgorithm sampling_algorithm = covering_ng::SamplingAlgorithm::SIZE_SAMPLING;
};
}

class Eval_CalcPpInc : public Manager {
public:
	Eval_CalcPpInc() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>(
				addBackend<SATModule<SATSettings1>>(
					addBackend<NewCoveringModule<internal::NewCoveringSettings>>()
				)
			)
		);
	}
};
} // namespace smtrat
