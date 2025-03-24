#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/NuCADModule/NuCADModule.h>
#include <smtrat-modules/NuCADModule/NuCADModule.tpp>
#include <smtrat-cadcells/operators/operator_mccallum_unified.h>


namespace smtrat {

namespace internal {
struct NuCADSettings : NuCADSettingsDefault  {
	using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
	using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
	using op = cadcells::operators::MccallumUnified<cadcells::operators::MccallumUnifiedSettingsComplete>;
	static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::GreedyMaxUnivariate;
};
}

class Eval_NucadPpDefault : public Manager {
public:
    Eval_NucadPpDefault() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<NuCADModule<internal::NuCADSettings>>()
            })
        );
	}
};

} // namespace smtrat
