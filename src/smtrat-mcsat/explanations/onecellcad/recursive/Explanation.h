#pragma once

#include "../OCStatistics.h"

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
struct NoHeuristic {
    static constexpr int heuristic = 0;
};
struct DegreeAscending {
    static constexpr int heuristic = 1;
};
struct DegreeDescending {
    static constexpr int heuristic = 2;
};


template<class Setting1, class Setting2>
struct Explanation {
	std::optional<mcsat::Explanation>
	operator()(const mcsat::Bookkeeping& trail, // current assignment state
			   carl::Variable var,
			   const FormulasT& trailLiterals, bool) const;
};

} // namespace recursive
} // namespace onecellcad
} // namespace mcsat
} // namespace smtrat
