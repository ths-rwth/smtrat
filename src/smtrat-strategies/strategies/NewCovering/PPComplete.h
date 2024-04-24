#pragma once

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.tpp>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {
struct NewCoveringSettings : NewCoveringSettings2 {
    using op = cadcells::operators::Mccallum<cadcells::operators::MccallumSettingsComplete>;
};
} // namespace internal

class NewCovering_PPComplete : public Manager {
public:
	NewCovering_PPComplete()
		: Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>(
				addBackend<SATModule<SATSettings1>>(
					addBackend<NewCoveringModule<internal::NewCoveringSettings>>())));
	}
};
} // namespace smtrat
