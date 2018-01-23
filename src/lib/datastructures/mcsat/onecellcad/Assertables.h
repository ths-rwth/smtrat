#pragma once

/**
 * @file
 * A collection of helper functions to check assertable conditions
 * for CAD properties, preconditions and invariants.
 */

#include <vector>
#include <set>
#include <algorithm>
#include <carl/core/Variable.h>
#include <carl/converter/CoCoAAdaptor.h>

namespace smtrat {
namespace onecellcad {

  template <typename PolyType>
  bool isNonConstantIrreducible(const PolyType& poly) {
    if (poly.isConstant())
      return false;
    else if (factorizer.irreducibleFactorsOf(poly).size() > 1)
      return false; // if more than 1 factor, not irreducible
    return true;
  }

  template <typename PolyType>
  bool containsOnlyNonConstantIrreduciblePolys(const std::vector<PolyType>& polys) {
    carl::CoCoAAdaptor<MultiPoly> factorizer(polys);
    for (const auto& poly : polys) {
      if (!isNonConstantIrreducible(poly))
        return false;
    }
    return true;
  }

  template <typename T>
  bool hasNoDuplicates(const std::vector<T>& container) {
    std::set<T> containerAsSet(container.begin(), container.end());
    return containerAsSet.size() == container.size();
  }

  template <typename T>
  bool isSubset(const std::vector<T>& c1, const std::vector<T> c2) {
    auto c1Copy = c1; // check if c1 is subset of c2
    auto c2Copy = c2;
    std::sort(c1.begin(), c1.begin());
    std::sort(c2.begin(), c2.begin());
    return c1.size() <= c2.size() &&
      std::includes(c2Copy, c1Copy);
  }

  template <typename PolyType>
  bool polyVariablesAreAllFromPredefinedSet(
      const std::vector<PolyType>& polys,
      const std::vector<carl::Variable> variables)
  {
    for (const auto& poly : polys) {
      if (!isSubset(poly.gatherVariables(), variables))
        return false
    }
    return true;
  }





} // namespace onecellcad
} // namespace smtrat
