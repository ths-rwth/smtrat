#pragma once

#include <vector>
#include <unordered_map>
#include <set>

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
#include <carl/converter/CoCoaAdaptor.h>
/* #include "Common.h" */
/* #include "projection/Projection.h" */
/* #include "lifting/LiftingTree.h" */
/* #include "helper/CADConstraints.h" */
/* #include "helper/CADCore.h" */
/* #include "helper/ConflictGraph.h" */
/* #include "helper/MISGeneration.h" */
/* #include "debug/TikzHistoryPrinter.h" */

namespace smtrat {
namespace opencad {

	using UnivarPoly = carl::UnivariatePolynomial<Rational>;
	using MultivarPoly = carl::MultivariatePolynomial<Rational>;
	using MultiUnivarPoly = carl::UnivariatePolynomial<MultivarPoly>;
	using RAN = carl::RealAlgebraicNumber<Rational>;
	using RANPoint = carl::RealAlgebraicPoint<Rational>;
	using RANMap = std::map<carl::Variable, RAN>;
  /**
   * Represent the "OpenCell Data Structure" from the 2012 Brown paper.
   * Design decision:
   * To reduce memory usage and improve performance we leave the variables,
   * variable order, universe dimension and cell dimension implicit
   * (they have to be stored in some form by the user if needed), since creating
   * multiple open cells would lead to multiple copies of variable lists/maps.
   */
  using OpenCADCell = std::vector<Sector>;
	/* using SampleLiftedWith = carl::Bitset; */
	/* using SampleRootOf = carl::Bitset; */
	/* using ConstraintSelection = carl::Bitset; */
	/* using OptionalPoly = boost::optional<const UPoly&>; */
	/* using OptionalID = boost::optional<std::size_t>; */
	/* using Assignment = std::map<carl::Variable, RAN>; */

  /**
   * Represent the algebraic boundaries (an open interval)
   * of a CADCell along a single axis k of the universe space.
   * This implies that the boundary polynomials are of level k, i.e.,
   * at most they mention the first k variables in the cell's variable ordering.
   * Design decision:
   * To reduce memory usage and improve performance we leave variable ordering,
   * the axis number k and thus the polynomials level implicit
   * (they have to be stored in some form by the user if needed).
   * Note that if 'lowBound' or 'highBound' is not defined, then this
   * represents negative and positive infinity, respectively.
   */
  struct sector {
    boost::optional<AlgebraicBound> lowBound;

    boost::optional<AlgebraicBound> highBound;

    bool isLowBoundNegativeInfty() {
      return lowBound == boost::none;
    }

    bool isHighBoundInfty() {
      return highBound == boost::none;
    }
  };

  /**
   * Weird combination of a polynomial and a real algebraic number found in the
   * Brown 2012 OpenCADCell paper.
   */
  struct AlgebraicBound {
    MultiUnivarPoly poly;
    RAN number;
  };

  /**
   * Construct a CADCell for the specified set of polynomials 'polySet'
   * that contains the specified 'point'. The returned cell represents
   * the largest region that is sign-invariant on all polynomials in
   * the 'polySet' and is cylindrical only with respect to the
	 * variables ordering specified in 'orderedVariables'.
	 * Note that this construction is only correct if plugging in
   * the 'point' into any polynomial of the 'polySet' yields a non-zero
   * value, i.e. 'point' is not a root of any polynomial in 'polySet',
	 * otherwise no CADCell is returned.
   * Note that the dimension (number of components) of the 'point' == the number of variables
   * in 'orderedVariables'
   * and that  any polynomial of the 'polySet' must be irreducible and
   * mention only variables from 'orderedVariables'.
	 *
   */
  boost::optional<CADCell> constructOpenCADCell(
    const std::vector<MultiUnivarPoly> polySet,
    const RANPoint& point,
    const std::vector<carl::Variable> orderedVariables)
  {
		// Note that combining 'orderedVariables' and 'point' into
		// a single object like Variable-to-RAN-map
		// is bad because a map may rearrange the variables and destroy
    // any desired variable ordering.
    assert(orderedVariables.size() == point.dim());

    CADCell cell = createUniverseCoveringOpenCADCell(point.dim());

    for(const auto& poly : polySet){
      if(boost::optional<CADCell> optionalCell
          = mergeCADCellWithPoly(cell, point, orderedVariables, poly)) {
        cell = optionalCell.value();
      }
      else {// If any merge fails, this whole construction fails too
        boost::optional<CADCell> fail;
        return fail;
      }
    }
    return boost::optional<CADCell>(cell);
  }



  /**
   * Merge the specified open CADCell 'cell' that contains the specified 'point'
   * (called "alpha" in the paper) with a polynomial 'poly'.
   * Before the merge 'cell' represents a region that is sign-invariant
   * on other (previously merged) polynomials (all signs are non-zero).
   * The returned cell represents a region that is additionally sign-invariant on
   * 'poly' (also with non-zero sign).
   * @return either a CADCell or nothing (representing FAIL but not an exception)
   */
  boost::optional<CADCell> mergeCADCellWithPoly(
    CADCell& cell,
    const RANPoint& point,
    const std::vector<carl::Variable> orderedVariables,
    const MultivarPoly poly)
	{
    size_t polyLevel = polyLevelOf(poly,orderedVariables);
    if(polyLevel == 0) // non-zero-constant-poly, no roots, so nothing to do
      return boost::optional<CADCell>(cell);
		carl::Variable mainVariable =
      orderedVariables[polyLevel];
    /* std::map<carl::Variable, Interval<Rational>> dummyMap; */

    RAN evaluation = carl::evaluate(poly, point, orderedVariables);
    // This merge function is only correct for a full-dimensional CADCells,
    // i.e. the 'point' is not allowed to be a root of 'poly'
    // since this implies a lower-dimensional cell.
    if(evaluation.isZero()) {
      boost::optional<CADCell> fail;
      return fail;
    }

		CADCell newCell = cell;
		if (polyLevel > 1) {
      // The "Open-McCallum projection closure" 'F' in the paper.
      std::vector<MultivarPoly> projectionPolys;
      // Add leading coefficient and discrimant
      projectionPolys.emplace_back(poly.lcoeff(mainVariable));
      MultiUnivarPoly polyAsUnivar = poly.toUnivariatePolynomial(mainVariable);
      projectionPolys.emplace_back(MultivarPoly(polyAsUnivar.discrimant()));

      // Add lowerBoundPoly resultant
      Sector& currentSector = cell[polyLevel]; // Called D[k] in the paper.
      if (!currentSector.isLowBoundNegativeInfty()) {
        UnivarPoly resultant = currentSector.lowBound.poly
          .toUnivariatePolynomial(mainVariable).resultant(polyAsUnivar);
        projectionPolys.push_back(MultivarPoly(resultant));
      }

      // Add upperBoundPoly resultant
      if (!currentSector.isHighBoundInfty()) {
        UnivarPoly resultant = currentSector.highBound.poly
          .toUnivariatePolynomial(mainVariable).resultant(polyAsUnivar);
        projectionPolys.push_back(MultivarPoly(resultant));
      }

      // Each poly in 'projectionPolys' must be factorized into its irreducible
      // factors.
      // Design decision: We use the CoCoA library as it seems to be
      // the fastest and most reliable library. Thus we need to enable
      // carl::cocoa in carl ccmake. Note that CoCoA needs to know the variable
      // names of the polynomials in every computation. The stateful
      // 'CoCoaAdaptor' takes care of that.
      CoCoAAdaptor<MultivarPoly> cocoaLib(projectionPolys);
      // Constant factors are irrelevant for root computations, so leave them out.
      const bool includeConstantFactors = false;
      for(MultivarPoly projPoly : projectionPolys) {
        for(const MultivarPoly& factor :
            cocoaLib.factorize(projPoly, includeConstantFactors))
        {
          if(boost::optional<CADCell> optionalCell
              = mergeCADCellWithPoly(newCell, point, projPoly)) {
            newCell = optionalCell.value();
          }
          else {// If submerge fails, this merge fails too
            boost::optional<CADCell> fail;
            return fail;
          }
        }
      }
    }

		// Isolate real roots of 'poly'.
		// 'alongPointPoly' is now a real univariate polynomial that only mentions the
		// 'mainVariable'
    std::unordered_map<carl::Variable, RAN> variableMap;
    for(int i = 0; i < polyLevel; i++)
      variableMap[orderedVariables[i]] = point[i];
    auto& roots = carl::rootfinder::realRoots(poly, reduceOneLevel(point), variableMap);

    RAN& lastPointCoordinate = point[point.size()-1];
    RAN& lowBoundNumber = newCell[polyLevel].lowBound.number;
    RAN& highBoundNumber = newCell[polyLevel].highBound.number;
    roots.push_back(lowBoundNumber);
    roots.push_back(highBoundNumber);
    roots.push_back(lastPointCoordinate);
    // TODO make unique
    sort(roots.begin(), roots.end(), roots);

		// Compare levelSectors and update levelSectors if there is a smaller sector
		RAN* previousRoot = nullptr;
		for(auto& root : roots) {
      if(root == lastPointCoordinate) {
        if(previousRoot != nullptr && *previousRoot != lowBoundNumber
            && *previousRoot != highBoundNumber)
          newCell[polyLevel].lowBound = {poly, *previousRoot};
        afterwardsRoot = root++;
        if(afterwardsRoot != nullptr && *afterwardsRoot != lowBoundNumber
            && *afterwardsRoot != highBoundNumber)
          newCell[polyLevel].highBound = {poly, *afterwardsRoot};
				break;
      }
      previousRoot = &root;
		}


    return newCell;
  }

  OpenCADCell createUniverseCoveringOpenCADCell(size_t universeDimension) {
    return OpenCADCell(universeDimension);
  }

  /**
   * Find the highest variable (with respect to the implicit variable ordering
   * in 'orderedVariables') that occurs with positive degree in 'poly' and
   * return its index in that variable ordering. This is called a polynomial's
   * level.
   */
  size_t polyLevelOf(const MultivarPoly& poly,
      const std::vector<carl::Variable> orderedVariables)
  {
    std::vector<carl::Variable> polyVariables(
        poly.gatherVariables().begin(),
        poly.gatherVariables.end());
    std::sort(polyVariables.begin(), polyVariables.end(),
        [&orderedVariables] (const carl::Variable& a, const carl::Variable& b) {
          return indexOf(a, orderedVariables) < indexOf(b, orderedVariables);
        });
    return indexOf(*polyVariables.last(), orderedVariables);
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

	RANPoint& reduceOneLevel(const RANPoint& point) {
    return reduceLevel(point, point.size()-1);
  }

  template<class T>
  std::vector<T> reduceLevel(const std::vector<T> v, Size_Type<T> newLevel) {
		assert( 0 <= newLevel && newLevel <= v.size());
    std::vector<T> newV;
		for(size_t i = 0; i < newLevel; i++)
			newV[i] = v[i];
		return newV;
  }

  template<class T>
  std::vector<T> reduceOneLevel(const std::vector<T> v) {
		assert( 0 <= newLevel && newLevel <= v.size());
    std::vector<T> newV(v.begin(), --v.end());
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
