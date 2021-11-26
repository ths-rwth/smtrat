#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>
#include "OCStatistics.h"

namespace smtrat::mcsat::onecell {

struct Explanation {
	#ifdef SMTRAT_DEVOPTION_Statistics
		OCStatistics& mStatistics = statistics_get<OCStatistics>("mcsat-explanation-onecell");
	#endif
	std::optional<mcsat::Explanation>
	operator()(const mcsat::Bookkeeping& trail, carl::Variable var, const FormulasT& reason, bool) const;
};

}