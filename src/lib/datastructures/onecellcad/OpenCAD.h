#pragma once

/**
 * @file
 * Construct a single open CAD Cell around a given point that is sign-invariant
 * on a given set of polynomials.
 *
 * References:
 * [1] Christopher W. Brown. 2013. Constructing a single open cell in a
 * cylindrical algebraic decomposition. In Proceedings of the 38th
 * International Symposium on Symbolic and Algebraic Computation (ISSAC '13).
 * ACM
 */

#include <vector>
#include <unordered_map>
#include <set>
#include <algorithm>

#include <boost/optional.hpp>

#include <carl/formula/model/ran/RealAlgebraicNumber.h>
#include <carl/formula/model/ran/RealAlgebraicNumberEvaluation.h>
#include <carl/formula/model/ran/RealAlgebraicPoint.h>
#include <carl/core/Variable.h>
#include <carl/core/VariablePool.h>
#include <carl/core/Resultant.h>
#include <carl/core/rootfinder/RootFinder.h>
#include <carl/core/UnivariatePolynomial.h>
#include <carl/core/MultivariatePolynomial.h>
#include <carl/converter/CoCoAAdaptor.h>

#include "../../Common.h" // type alias for Rational number representation
/* #include "projection/Projection.h" */
/* #include "lifting/LiftingTree.h" */
/* #include "helper/CADConstraints.h" */
/* #include "helper/CADCore.h" */
/* #include "helper/ConflictGraph.h" */
/* #include "helper/MISGeneration.h" */
/* #include "debug/TikzHistoryPrinter.h" */

namespace smtrat {
namespace opencad {
  // Forward declarations
  struct Sector;
  struct Section;

	using UniPoly = carl::UnivariatePolynomial<Rational>;
	using MultiPoly = carl::MultivariatePolynomial<Rational>;
	using MultiUnivarPoly = carl::UnivariatePolynomial<MultiPoly>;
	using RAN = carl::RealAlgebraicNumber<Rational>;
	using RANPoint = carl::RealAlgebraicPoint<Rational>;
	using RANMap = std::map<carl::Variable, RAN>;
  /**
   * Represent an "open cell" [1]
   * TODO reduce phrasing
   * Design decision:
   * To reduce memory usage and improve performance we leave the variables,
   * variable order, universe dimension and cell dimension implicit
   * (they have to be stored in some form by the user if needed), since creating
   * multiple open cells would lead to multiple copies of variable lists/maps.
   */
  using OpenCell = std::vector<Sector>;
	/* using SampleLiftedWith = carl::Bitset; */
	/* using SampleRootOf = carl::Bitset; */
	/* using ConstraintSelection = carl::Bitset; */
	/* using OptionalPoly = boost::optional<const UPoly&>; */
	/* using OptionalID = boost::optional<std::size_t>; */
	/* using Assignment = std::map<carl::Variable, RAN>; */

  /**
   * TODO check phrasing
   * Represent the algebraic boundaries (an open interval)
   * of a OpenCell along a single axis k of the universe space.
   * This implies that the boundary polynomials are of level k, i.e.,
   * at most they mention the first k variables in the cell's variable ordering.
   * Design decision:
   * To reduce memory usage and improve performance we leave variable ordering,
   * the axis number k and thus the polynomials level implicit
   * (they have to be stored in some form by the user if needed).
   * Note that if 'lowBound' or 'highBound' is not defined, then this
   * represents negative and positive infinity, respectively.
   */
  struct Sector {
    boost::optional<Section> lowBound;

    boost::optional<Section> highBound;

    bool isLowBoundNegativeInfty() {
      return lowBound == boost::none;
    }

    bool isHighBoundInfty() {
      return highBound == boost::none;
    }
  };

  /**
   * TODO check phrasing and compare to implementation.
   * TODO enable representing +-infty?
   * Cell section with cached value similar to [1].
   * This is basically a function f: algReal^{k-1} -> algReal; from
   * multi-dimensional point of level k-1 (whose components are algebraic reals)
   * to an algebraic real. [1] uses an unnecessary complicated way to represent
   * this function. For performance we cache the result of plugging in the
   * first k-1 components of a special point (called alpha in [1]).
   * If the plugged-in point is of level k-1, then this section is said to be
   * of level k, because it defines the boundaries along the k-th axis.
   */
  struct Section {
    /**
     * Must be an irreducible poly of level k.
     * TODO explain design choice
     */
    MultiUnivarPoly poly;
    /**
     * TODO after plugging in a special point called alpha in [1].
     * TODO refactor out if section is usefull without cached point.
     */
    RAN cachedPoint;
  }


  /**
   * TODO check phrasing
   * Construct a OpenCell for the given set of polynomials 'polySet'
   * that contains the given 'point'. The returned cell represents
   * the largest region that is sign-invariant on all polynomials in
   * the 'polySet' and is cylindrical only with respect to the
	 * variables ordering given in 'variableOrder'.
	 * Note that this construction is only correct if plugging in
   * the 'point' into any polynomial of the 'polySet' yields a non-zero
   * value, i.e. 'point' is not a root of any polynomial in 'polySet',
	 * otherwise no OpenCell is returned.
   * Note that the dimension (number of components) of the 'point' == the number of variables
   * in 'variableOrder'
   * and that  any polynomial of the 'polySet' must be irreducible and
   * mention only variables from 'variableOrder'.
	 *
   */
  boost::optional<OpenCell> constructOpenCADCell(
    const std::vector<MultiPoly> polySet,
    const RANPoint& point,
    const std::vector<carl::Variable> variableOrder)
  {
		// Note that combining 'variableOrder' and 'point' into
		// a single object like Variable-to-RAN-map
		// is bad because a map may rearrange the variables and destroy
    // any desired variable ordering.
    assert(variableOrder.size() == point.dim());

    OpenCell cell = createFullspaceCoveringCell(point.dim());

    for(const auto& poly : polySet){
      if(boost::optional<OpenCell> optionalCell
          = mergeCellWithPoly(cell, point, variableOrder, poly)) {
        cell = optionalCell.value();
      }
      else {// If any merge fails, this whole construction fails too
        boost::optional<OpenCell> fail;
        return fail;
      }
    }
    return boost::optional<OpenCell>(cell);
  }



  /**
   * Merge the given open OpenCell 'cell' that contains the given 'point'
   * (called "alpha" in the paper) with a polynomial 'poly'.
   * Before the merge 'cell' represents a region that is sign-invariant
   * on other (previously merged) polynomials (all signs are non-zero).
   * The returned cell represents a region that is additionally sign-invariant on
   * 'poly' (also with non-zero sign).
   * @return either a OpenCell or nothing (representing FAIL but not an exception)
   */
  boost::optional<OpenCell> mergeCellWithPoly(
    OpenCell& cell,
    const RANPoint& point,
    const std::vector<carl::Variable> variableOrder,
    const MultiPoly poly)
	{
    size_t polyLevel = polyLevel(poly,variableOrder);
    if(polyLevel == 0) // non-zero-constant-poly, no roots, so nothing to do
      return boost::optional<OpenCell>(cell);
		carl::Variable mainVariable =
      variableOrder[polyLevel-1];

    // Use a special function because we plug in algebraic reals into the poly.
    RAN evaluation = carl::evaluate(poly,
        reduceLevel(point, polyLevel),
        reduceLevel(variableOrder, polyLevel));
    // This merge function is only correct for a full-dimensional CADCells,
    // i.e. the 'point' is not allowed to be a root of 'poly'
    // since this implies a lower-dimensional cell.
    if(evaluation.isZero()) {
      boost::optional<OpenCell> fail;
      return fail;
    }

		OpenCell newCell = cell;
		if (polyLevel > 1) {
      MultiUnivarPoly polyAsUnivar = poly.toUnivariatePolynomial(mainVariable);
      // The "Open-McCallum projection" (called 'F' in [1]) of the to-be-merged
      // poly.
      std::vector<MultiPoly> projectionPolys;
      // Add leading coefficient and discrimant
      projectionPolys.emplace_back(polyAsUnivar.lcoeff());
      projectionPolys.emplace_back(MultiPoly(polyAsUnivar.discrimant()));

      // Add lowerBoundPoly resultant
      Sector& currentSector = cell[polyLevel-1]; // Called D[k] in [1]
      if (!currentSector.isLowBoundNegativeInfty()) {
        UniPoly resultant = currentSector.lowBound.poly
          .toUnivariatePolynomial(mainVariable).resultant(polyAsUnivar);
        projectionPolys.push_back(MultiPoly(resultant));
      }

      // Add upperBoundPoly resultant
      if (!currentSector.isHighBoundInfty()) {
        UniPoly resultant = currentSector.highBound.poly
          .toUnivariatePolynomial(mainVariable).resultant(polyAsUnivar);
        projectionPolys.push_back(MultiPoly(resultant));
      }

      // Each poly in 'projectionPolys' must be factorized into its irreducible
      // factors.
      // Design decision: We use the CoCoA library as it seems to be
      // the fastest and most reliable library. Thus we need to enable
      // carl::cocoa in carl ccmake. Note that CoCoA needs to know the variable
      // names of the polynomials in every computation. The stateful
      // 'CoCoaAdaptor' and its constructor take care of that.
      CoCoAAdaptor<MultiPoly> cocoaLib(projectionPolys);
      for(MultiPoly& projPoly : projectionPolys) {
        // Constant factors are irrelevant for root computations, so leave them out.
        const bool keepConstFactorsFlag = false;
        for(const MultiPoly& factor :
            cocoaLib.factorize(projPoly, keepConstFactorsFlag))
        {
          if(boost::optional<OpenCell> optionalCell
              = mergeCellWithPoly(newCell, point, projPoly))
          {
            newCell = optionalCell.value();
          }
          else {// If submerge fails, this merge fails too
            boost::optional<OpenCell> fail;
            return fail;
          }
        }
      }
    }

    std::unordered_map<carl::Variable, RAN> pointAsMap;
    for(int i = 0; i < polyLevel-1; i++)
      pointAsMap[variableOrder[i]] = point[i];

		// Isolate real roots of level-k 'poly' after plugin in a level-(k-1) point.
    // polyLevel is >= 1
    RAN point_k = point[polyLevel-1]; // called alpha_k in [1]
    // Roots are represented as algebraic reals.
    auto& roots = carl::rootfinder::realRoots(poly, pointAsMap);
    std::sort(roots.begin(), roots.end());

    // Search for roots that are closest to point_k s.t.
    // someRoot ... < root_lower < point_k < root_higher < ... someOtherRoot
    auto root_higher = std::find_if(
        roots.begin(),
        roots.end(),
        [&point_k] (const RAN& otherPoint) { return otherPoint > point_k; });
    // Update high bound if a tighter root is found s.t.
    // point_k < root_higher < old_root_higher
    if(root_higher != roots.end() &&
        *root_higher < currentSector.highBound.cachedPoint) {
      currentSector.highBound.poly = poly;
      currentSector.highBound.cachedPoint = *root_higher;
    }
    // Update low bound if a tighter root is found s.t.
    // old_root_lower < root_lower < point_k
    if(root_higher != roots.begin()) {
      auto root_lower = --root_higher;
      if(*root_lower > currentSector.lowBound.cachedPoint) {
      currentSector.lowBound.poly = poly;
      currentSector.lowBound.cachedPoint = *root_lower;
    }

    return newCell;
  }

  OpenCell createFullspaceCoveringCell(size_t level) {
    return OpenCell(level);
  }

  /**
   * Find the highest variable (with respect to the ordering
   * in 'variableOrder') that occurs with positive degree in 'poly' and
   * return its index+1 in that variable ordering.
   * +1 because level count starts at 1, but index at 0.
   */
  size_t polyLevel(const MultiPoly& poly,
      const std::vector<carl::Variable> variableOrder)
  {
    std::vector<carl::Variable> polyVariables(
        poly.gatherVariables().begin(),
        poly.gatherVariables.end());

    std::sort(polyVariables.begin(), polyVariables.end(),
        [&variableOrder] (const carl::Variable& a, const carl::Variable& b)
        {
          return indexOf(a, variableOrder) < indexOf(b, variableOrder);
          /* std:distance(values.begin(), std::find(values.begin(), values.end(), value) */
        });
    return 1+indexOf(*polyVariables.last(), variableOrder);
  }


	/**
   * Copy and only retain the first 'newLevel' number of components of an n
   * dimensional 'point'. 'newLevel' must be within the dimension bounds: 0 <=
   * newLevel <= n FIX make this a member function of RANPoint?
	 */
	RANPoint& reduceLevel(const RANPoint& point, size_t newLevel) {
		assert( 0 <= newLevel && newLevel <= point.dim());
		RANPoint& lowerDimPoint;
		for(size_t i = 0; i < newLevel; i++)
			lowerDimpoint[i] = point[i];
		return lowerDimPoint;
	}

  template<class T>
  std::vector<T> reduceLevel(const std::vector<T> v, Size_Type<T> newLevel) {
		assert( 0 <= newLevel && newLevel <= v.size());
    std::vector<T> newV;
		for(size_t i = 0; i < newLevel; i++)
			newV[i] = v[i];
		return newV;
  }

  /**
   * Find the index of a 'value' among 'values'.
   * 'value' must exist among 'values'.
   */
  template<class T>
  size_t indexOf(T value, const std::vector<T> values) {
    return std::find(values.begin(), values.end(), value) - values.begin();
  }


  /**
   * Function object to compare and sort variables inside any standard container.
   */
  struct VariableCompare {
    const std::unordered_map<carl::Variable, int> variableToIndex;

    bool operator()(const carl::Variable& a, const carl::Variable& b) {
      return variableToIndex[a] < variableToIndex[b];
    }
  };

} // namespace opencad
} // namespace smtrat
