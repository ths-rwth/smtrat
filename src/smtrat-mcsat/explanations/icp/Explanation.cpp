#include "Explanation.h"

#include "IntervalPropagation.h"

namespace smtrat {
namespace mcsat {
namespace icp {

boost::optional<mcsat::Explanation> Explanation::operator()(const mcsat::Bookkeeping& data, carl::Variable /*var*/, const FormulasT& reason, bool force_use_core) const {
	#ifdef SMTRAT_DEVOPTION_Statistics
    mStatistics.explanationCalled();
    #endif

	const FormulasT& constr = [&]() -> const FormulasT& {
		if (force_use_core) return reason;
		else return data.constraints();
	}();
	SMTRAT_LOG_DEBUG("smtrat.mcsat.icp", "Explain conflict " << constr);

	IntervalPropagation ip(std::vector<carl::Variable>(data.variables().begin(), data.variables().end()), constr, data.model());
	auto res = ip.execute();
	if (res) {
		#ifdef SMTRAT_DEVOPTION_Statistics
        mStatistics.explanationSuccess();
        #endif
		SMTRAT_LOG_DEBUG("smtrat.mcsat.icp", "Got conflict " << *res);
		return mcsat::Explanation(*res);
	} else {
		return boost::none;
	}

}

}
}
}
