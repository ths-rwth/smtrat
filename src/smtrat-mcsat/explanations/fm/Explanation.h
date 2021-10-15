#pragma once

#include <smtrat-mcsat/smtrat-mcsat.h>

#include "FMStatistics.h"

namespace smtrat {
namespace mcsat {
namespace fm {

struct DefaultSettings {
	static constexpr bool use_all_constraints = false;
};
struct IgnoreCoreSettings {
	static constexpr bool use_all_constraints = true;
};

template<class Settings>
struct Explanation {

#ifdef SMTRAT_DEVOPTION_Statistics
	FMStatistics& mStatistics = statistics_get<FMStatistics>("mcsat-explanation-fm");
#endif

	boost::optional<mcsat::Explanation> operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason, bool force_use_core) const;

};

}
}
}
