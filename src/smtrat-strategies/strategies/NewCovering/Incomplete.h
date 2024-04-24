#pragma once

#include <smtrat-modules/NewCoveringModule/NewCoveringModule.tpp>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {
struct NewCoveringSettings : NewCoveringSettings2 {
	using op = cadcells::operators::Mccallum<cadcells::operators::MccallumSettings>;
};
} // namespace internal

class NewCovering_Incomplete : public Manager {
public:
	NewCovering_Incomplete()
		: Manager() {
		setStrategy(
			addBackend<SATModule<SATSettings1>>(
				addBackend<NewCoveringModule<internal::NewCoveringSettings>>()));
	}
};
} // namespace smtrat
