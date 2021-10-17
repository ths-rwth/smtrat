#pragma once

#include "VSStatistics.h"

#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat {
namespace mcsat {
namespace vs {

struct Explanation {

#ifdef SMTRAT_DEVOPTION_Statistics
	VSStatistics& mStatistics = statistics_get<VSStatistics>("mcsat-explanation-vs");
#endif

	boost::optional<mcsat::Explanation> operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason, bool) const;
};

}
}
}
