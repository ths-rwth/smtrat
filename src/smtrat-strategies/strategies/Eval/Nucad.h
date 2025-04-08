#pragma once

#include <smtrat-solver/Manager.h>


#include <smtrat-modules/NuCADModule/NuCADModule.h>
#include <smtrat-modules/NuCADModule/NuCADModule.tpp>
#include <smtrat-cadcells/operators/operator_mccallum_unified.h>


namespace smtrat {

namespace internal {
struct NuCADSettings : NuCADSettingsDefault  {
	using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
	using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
	using op = cadcells::operators::MccallumUnified<cadcells::operators::MccallumUnifiedSettingsComplete>;
	static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::FeatureBasedPickering;
	static constexpr bool move_boolean_variables_to_front = true;
};
}

class Eval_Nucad : public Manager {
public:
    Eval_Nucad() : Manager() {
		setStrategy(
			
                addBackend<NuCADModule<internal::NuCADSettings>>()
            
        );
	}
};

} // namespace smtrat
