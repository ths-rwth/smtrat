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

	std::optional<mcsat::Explanation> operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason, bool force_use_core) const;
};

}
}
}
