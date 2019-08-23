#pragma once

#include <lib/datastructures/mcsat/fm/Explanation.h>

#include <smtrat-mcsat/assignments/arithmetic/AssignmentFinder.h>
#include <smtrat-mcsat/assignments/smtaf/AssignmentFinder.h>
#include <smtrat-mcsat/assignments/SequentialAssignment.h>
#include <smtrat-mcsat/explanations/ParallelExplanation.h>
#include <smtrat-mcsat/explanations/SequentialExplanation.h>
#include <smtrat-mcsat/explanations/icp/Explanation.h>
#include <smtrat-mcsat/explanations/nlsat/Explanation.h>
#include <smtrat-mcsat/explanations/onecellcad/Explanation.h>
#include <smtrat-mcsat/explanations/vs/Explanation.h>
#include <smtrat-mcsat/variableordering/VariableOrdering.h>

namespace smtrat {
namespace mcsat {

struct MCSATSettingsNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<nlsat::Explanation>;
};

//OneCell only
struct MCSATSettingsOC {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<onecellcad::Explanation, nlsat::Explanation>;
};
struct MCSATSettingsFMVSOC {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	//using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,vs::Explanation,onecellcad::Explanation, nlsat::Explanation>;
};

struct MCSATSettingsFMNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	// using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,nlsat::Explanation>;
};

struct MCSATSettingsVSNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<vs::Explanation,nlsat::Explanation>;
};

struct MCSATSettingsFMVSNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,vs::Explanation,nlsat::Explanation>;
};

struct MCSATSettingsICPNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<icp::Explanation,nlsat::Explanation>;
};

}
}
