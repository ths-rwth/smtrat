#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

#include "ICPStatistics.h"

namespace smtrat {
namespace mcsat {
namespace icp {

struct Explanation {
#ifdef SMTRAT_DEVOPTION_Statistics
	ICPStatistics& mStatistics = statistics_get<ICPStatistics>("mcsat-explanation-icp");
#endif

	boost::optional<mcsat::Explanation> operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason) const;
};

}
}
}
