#pragma once 

#include "types.h"
#include <functional>
#include <boost/container/flat_set.hpp>

namespace smtrat::covering_ng::formula {

using ImplicantOrdering = std::function<bool(const boost::container::flat_set<cadcells::Constraint>&, const boost::container::flat_set<cadcells::Constraint>&)>;

using ConstraintOrdering = std::function<bool(const cadcells::Constraint&, const cadcells::Constraint&)>;

enum class Valuation {
    TRUE, FALSE, MULTIVARIATE, UNKNOWN 
};
inline std::ostream& operator<<(std::ostream& o, Valuation v) {
    if (v == Valuation::TRUE)  o << "TRUE";
    else if (v == Valuation::FALSE)  o << "FALSE";
    else if (v == Valuation::MULTIVARIATE)  o << "MULTIVARIATE";
    else o << "UNKNOWN";
    return o;
}

}