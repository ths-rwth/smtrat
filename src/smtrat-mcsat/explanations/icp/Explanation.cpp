#include "Explanation.h"

#include "IntervalPropagation.h"

namespace smtrat {
namespace mcsat {
namespace icp {

boost::optional<mcsat::Explanation> Explanation::operator()(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason) const {
	SMTRAT_LOG_DEBUG("smtrat.mcsat.icp", "Explain conflict " << reason);

	IntervalPropagation ip(data.variableOrder(), data.constraints(), data.model());
	auto res = ip.execute();
	if (res) {
		return mcsat::Explanation(*res);
	} else {
		return boost::none;
	}

}

}
}
}
