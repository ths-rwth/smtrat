#pragma once

#include "../../../datastructures/mcsat/arithmetic/AssignmentFinder_arithmetic.h"
#include "../../../datastructures/mcsat/explanations/ParallelExplanation.h"
#include "../../../datastructures/mcsat/explanations/SequentialExplanation.h"
#include "../../../datastructures/mcsat/fm/Explanation.h"
#include "../../../datastructures/mcsat/nlsat/Explanation.h"
#include "../../../datastructures/mcsat/vs/Explanation.h"
#include "../../../datastructures/mcsat/variableordering/VariableOrdering.h"

namespace smtrat {
namespace mcsat {

struct MCSATSettings1 {
	static constexpr VariableOrdering variable_ordering = VariableOrdering::FeatureBased;
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	//using ExplanationBackend = fm::Explanation;
	//using ExplanationBackend = mcsat::ParallelExplanation<nlsat::Explanation,nlsat::Explanation>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation,nlsat::Explanation>;
};

}
}
