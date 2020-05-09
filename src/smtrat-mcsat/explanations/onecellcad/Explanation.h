#pragma once

#include "OCStatistics.h"

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat {
namespace mcsat {
namespace onecellcad {

struct Explanation {

#ifdef SMTRAT_DEVOPTION_Statistics
	OCStatistics& mStatistics = statistics_get<OCStatistics>("mcsat-explanation-onecellcad");
#endif

	boost::optional<mcsat::Explanation>
	operator()(const mcsat::Bookkeeping& trail, // current assignment state
			   carl::Variable var,
			   const FormulasT& trailLiterals, bool covering_at_first_level=true) const;
};

} // namespace onecellcad
} // namespace mcsat
} // namespace smtrat
