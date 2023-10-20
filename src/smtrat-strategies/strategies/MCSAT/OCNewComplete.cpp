#include "OCNewComplete.h"

#include <smtrat-solver/Manager.h>

// #include "../modules/FPPModule/FPPModule.h"
#include <smtrat-modules/SATModule/SATModule.tpp>


namespace smtrat {

namespace internal {
struct OCSettings : smtrat::mcsat::onecell::DefaultSettings {
	constexpr static auto op = cadcells::operators::op::mccallum_complete;
};

struct SATSettings : smtrat::SATSettingsMCSAT {
	struct MCSATSettings : mcsat::Base {
		using AssignmentFinderBackend = mcsat::arithmetic::AssignmentFinder;
		using ExplanationBackend = mcsat::SequentialExplanation<mcsat::onecell::Explanation<OCSettings>, mcsat::nlsat::Explanation>;
	};
};
} // namespace internal


MCSAT_OCNewComplete::MCSAT_OCNewComplete()
	: Manager() {
	setStrategy(
		addBackend<SATModule<internal::SATSettings>>());
}

} // namespace smtrat
