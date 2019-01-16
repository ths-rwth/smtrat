#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat {
namespace mcsat {
namespace onecellcad {

struct Explanation {
	boost::optional<mcsat::Explanation>
	operator()(const mcsat::Bookkeeping& trail, // current assignment state
			   const std::vector<carl::Variable>& varOrder,
			   carl::Variable var,
			   const FormulasT& trailLiterals) const;
};

} // namespace onecellcad
} // namespace mcsat
} // namespace smtrat
