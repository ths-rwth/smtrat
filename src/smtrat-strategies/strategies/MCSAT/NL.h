#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat {

namespace internal {

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::nlsat::Explanation>;
	};
};

}

class MCSAT_NL: public Manager {
	public:
		MCSAT_NL(): Manager() {
			setStrategy(
				addBackend<SATModule<internal::SATSettings>>()
			);
		}
};
}	// namespace smtrat
