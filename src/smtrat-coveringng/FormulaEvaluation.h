#pragma once 

#include "types.h"
#include <functional>
#include <boost/container/flat_set.hpp>

namespace smtrat::covering_ng::formula {

using ImplicantOrdering = std::function<bool(cadcells::datastructures::Projections&, const boost::container::flat_set<cadcells::datastructures::PolyConstraint>&, const boost::container::flat_set<cadcells::datastructures::PolyConstraint>&)>;

using ConstraintOrdering = std::function<bool(cadcells::datastructures::Projections&, const cadcells::datastructures::PolyConstraint&, const cadcells::datastructures::PolyConstraint&)>;

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