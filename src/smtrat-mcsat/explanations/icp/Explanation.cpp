#include "Explanation.h"

#include "IntervalPropagation.h"

namespace smtrat {
namespace mcsat {
namespace icp {

boost::optional<mcsat::Explanation> Explanation::operator()(const mcsat::Bookkeeping& data, carl::Variable /*var*/, const FormulasT& /*reason*/) const {
	#ifdef SMTRAT_DEVOPTION_Statistics
    mStatistics.explanationCalled();
    #endif

	SMTRAT_LOG_DEBUG("smtrat.mcsat.icp", "Explain conflict " << data.constraints());

	IntervalPropagation ip(std::vector<carl::Variable>(data.variables().begin(), data.variables().end()), data.constraints(), data.model());
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
