#include "OCNew.h"

#include <smtrat-solver/Manager.h>

// #include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.tpp>


namespace smtrat {

namespace internal {
struct OCSettings : smtrat::mcsat::onecell::DefaultSettings {
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using AssignmentFinderBackend = mcsat::arithmetic::AssignmentFinder;
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::onecell::Explanation<OCSettings>, mcsat::nlsat::Explanation>;
	};
};
} // namespace internal


MCSAT_OCNew::MCSAT_OCNew()
	: Manager() {
	setStrategy(
		addBackend<SATModule<internal::SATSettings>>());
}

} // namespace smtrat
