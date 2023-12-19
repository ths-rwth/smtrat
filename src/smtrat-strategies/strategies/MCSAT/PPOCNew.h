#pragma once

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.tpp>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {
struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using AssignmentFinderBackend = mcsat::arithmetic::AssignmentFinder;
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::onecell::Explanation<smtrat::mcsat::onecell::DefaultSettings>, mcsat::nlsat::Explanation>;
	};
};
} // namespace internal

class MCSAT_PPOCNew : public Manager {
public:
	MCSAT_PPOCNew() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
				addBackend<SATModule<internal::SATSettings>>()
			})
		);
	}
};

} // namespace smtrat
