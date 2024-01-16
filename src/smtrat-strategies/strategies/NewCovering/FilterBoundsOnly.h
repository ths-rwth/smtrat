#pragma once

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
	constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_FILTER;
};
} // namespace internal

class NewCovering_PPFilterBoundsOnly : public Manager {
public:
	NewCovering_PPFilterBoundsOnly()
		: Manager() {
		setStrategy(
			addBackend<SATModule<SATSettings1>>(
				addBackend<NewCoveringModule<internal::NewCoveringSettings>>()));
	}
};
} // namespace smtrat
