#pragma once

/**
 * @file
 * A collection of helper functions to check assertable conditions
 * for CAD properties, preconditions and invariants.
 */

#include <carl-arith/poly/umvpoly/MultivariatePolynomial.h>
#include <carl-arith/core/Variable.h>
#include <carl-arith/poly/umvpoly/functions/Factorization.h>
#include <smtrat-common/smtrat-common.h>

#include <algorithm>
#include <set>
#include <vector>

namespace smtrat {
namespace mcsat {
namespace onecellcad {

template<typename PolyType>
bool hasOnlyNonConstIrreducibles(const std::vector<PolyType>& polys) {
	if (polys.empty()) // Corner case, COCOA crashes on empty poly-vector
		return true;
	for (const auto& poly : polys) {
		if (poly.is_constant())
			return false;
		else if (carl::irreducible_factors(poly, false).size() > 1)
			return false;
		// if more than 1 factor, not irreducible
	}
	return true;
}

template<typename PolyType>
bool isNonConstIrreducible(const PolyType& poly) {
	return hasOnlyNonConstIrreducibles<PolyType>({poly});
}

template<typename T>
bool hasUniqElems(const std::vector<T>& container) {
	std::set<T> containerAsSet(container.begin(), container.end());
	return containerAsSet.size() == container.size();
}

template<typename T>
bool isSubset(const std::vector<T>& c1, const std::vector<T>& c2) {
	auto c1Copy{c1}; // check if c1 is subset of c2
	auto c2Copy{c2};
	std::sort(c1Copy.begin(), c1Copy.end());
	std::sort(c2Copy.begin(), c2Copy.end());
	return c1Copy.size() <= c2Copy.size() &&
		   std::includes(c2Copy.begin(), c2Copy.end(), c1Copy.begin(), c1Copy.end());
}

template<typename T>
std::vector<T> asVector(const std::set<T> s) {
	std::vector<T> vec(s.begin(), s.end());
	return vec;
}

/* template <typename T> */
/* bool isSubset(const std::set<T>& c1, const std::vector<T> c2) { */
/*   return isSubset(c1AsVec, c2); */
/* } */

template<typename PolyType>
bool polyVarsAreAllInList(
	const std::vector<PolyType>& polys,
	const std::vector<carl::Variable>& variables) {
	for (const auto& poly : polys) {
		if (!isSubset<carl::Variable>(carl::variables(poly).as_vector(), variables))
			return false;
	}
	return true;
}

} // namespace onecellcad_lw
} // namespace mcsat
} // namespace smtrat
