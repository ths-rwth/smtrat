#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat {
namespace mcsat {
namespace icp {

struct Explanation {
	boost::optional<mcsat::Explanation> operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason) const;
};

}
}
}
