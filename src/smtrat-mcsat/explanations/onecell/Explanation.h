#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat::mcsat::onecell {

struct Explanation {
	std::optional<mcsat::Explanation>
	operator()(const mcsat::Bookkeeping& trail, carl::Variable var, const FormulasT& reason, bool) const;
};

}