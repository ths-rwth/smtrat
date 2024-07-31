#pragma once

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.tpp>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {
struct OpSettings : cadcells::operators::MccallumFilteredSettings {
	static constexpr DelineationFunction delineation_function = BOUNDS_ONLY;
    static constexpr bool enable_weak = true;
};

struct NewCoveringSettings : NewCoveringSettings2 {
	using op = cadcells::operators::MccallumFiltered<OpSettings>;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;
};
} // namespace internal

class NewCovering_PPFilterBoundsOnly : public Manager {
public:
	NewCovering_PPFilterBoundsOnly()
		: Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>(
				addBackend<SATModule<SATSettings1>>(
					addBackend<NewCoveringModule<internal::NewCoveringSettings>>())));
	}
};
} // namespace smtrat
