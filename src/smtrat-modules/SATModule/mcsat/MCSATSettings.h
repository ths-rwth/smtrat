#pragma once

#include <smtrat-mcsat/assignments/arithmetic/AssignmentFinder.h>
#include <smtrat-mcsat/assignments/smtaf/AssignmentFinder.h>
#include <smtrat-mcsat/assignments/SequentialAssignment.h>
#include <smtrat-mcsat/explanations/ParallelExplanation.h>
#include <smtrat-mcsat/explanations/SequentialExplanation.h>
#include <smtrat-mcsat/explanations/icp/Explanation.h>
#include <smtrat-mcsat/explanations/nlsat/Explanation.h>
#include <smtrat-mcsat/explanations/onecellcad/recursive/Explanation.h>
#include <smtrat-mcsat/explanations/onecellcad/levelwise/Explanation.h>
#include <smtrat-mcsat/explanations/vs/Explanation.h>
#include <smtrat-mcsat/explanations/fm/Explanation.h>
#include <smtrat-mcsat/variableordering/VariableOrdering.h>
#include <smtrat-mcsat/explanations/onecell/Explanation.h>

namespace smtrat::mcsat {

struct Base {
	static constexpr bool early_evaluation = false;
	using AssignmentFinderBackend = smtrat::mcsat::arithmetic::AssignmentFinder;
};

struct MCSATSettingsDefault : Base  {
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,
													 icp::Explanation,
													 vs::Explanation,
													 onecell::Explanation<onecell::DefaultSettings>>;
};

struct MCSATSettingsOC : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<onecell::Explanation<onecell::DefaultSettings>>;
};

}
