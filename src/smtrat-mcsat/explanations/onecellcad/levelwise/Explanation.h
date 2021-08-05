#pragma once

#include "OCStatistics.h"

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat {
namespace mcsat {
namespace onecellcad {
namespace levelwise {


struct SectionHeuristic1 {
	static constexpr int sectionHeuristic = 1;
};
struct SectionHeuristic2 {
	static constexpr int sectionHeuristic = 2;
};
struct SectionHeuristic3 {
	static constexpr int sectionHeuristic = 3;
};

struct SectorHeuristic1 {
	static constexpr int sectorHeuristic = 1;
};
struct SectorHeuristic2 {
	static constexpr int sectorHeuristic = 2;
};
struct SectorHeuristic3 {
	static constexpr int sectorHeuristic = 3;
};


template<class Setting1, class Setting2>
struct Explanation {

#ifdef SMTRAT_DEVOPTION_Statistics
	OCStatistics& mStatistics = statistics_get<OCStatistics>("mcsat-explanation-onecellcad-lw");
#endif

	boost::optional<mcsat::Explanation>
	operator()(const mcsat::Bookkeeping& trail, // current assignment state
			   carl::Variable var,
			   const FormulasT& trailLiterals) const;
};

} // namespace levelwise
} // namespace onecellcad
} // namespace mcsat
} // namespace smtrat
