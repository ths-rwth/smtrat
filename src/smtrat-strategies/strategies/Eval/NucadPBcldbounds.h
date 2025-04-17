#pragma once

#include <smtrat-solver/Manager.h>


#include <smtrat-modules/NuCADModule/NuCADModule.h>
#include <smtrat-modules/NuCADModule/NuCADModule.tpp>
#include <smtrat-cadcells/operators/operator_mccallum_unified.h>


namespace smtrat {

namespace internal {
struct NuCADSettings : NuCADSettingsDefault  {
	using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
	struct OpSettings : cadcells::operators::MccallumUnifiedSettingsComplete {
		static constexpr DelineationFunction delineation_function = BOUNDS_ONLY;
		static constexpr bool enable_weak = true;
	};
	using op = cadcells::operators::MccallumUnified<OpSettings>;
	static constexpr covering_ng::variables::VariableOrderingHeuristics variable_ordering_heuristic = covering_ng::variables::VariableOrderingHeuristics::FeatureBasedPickering;
	static constexpr bool move_boolean_variables_to_front = true;
	static constexpr bool enable_weak = true;
};
}

class Eval_NucadPBcldbounds : public Manager {
public:
    Eval_NucadPBcldbounds() : Manager() {
		setStrategy(
			
                addBackend<NuCADModule<internal::NuCADSettings>>()
            
        );
	}
};

} // namespace smtrat
