#pragma once

#include "OCStatistics.h"

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat {
namespace mcsat {
namespace onecellcad {
namespace recursive {

struct CoverNullification {
	static constexpr bool cover_nullification = true;
};
struct DontCoverNullification {
	static constexpr bool cover_nullification = false;
};


template<class Settings>
struct Explanation {

#ifdef SMTRAT_DEVOPTION_Statistics
	OCStatistics& mStatistics = statistics_get<OCStatistics>("mcsat-explanation-onecellcad");
#endif

	boost::optional<mcsat::Explanation>
	operator()(const mcsat::Bookkeeping& trail, // current assignment state
			   carl::Variable var,
			   const FormulasT& trailLiterals) const;
};

} // namespace recursive
} // namespace onecellcad
} // namespace mcsat
} // namespace smtrat
