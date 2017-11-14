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
namespace onecellcad {

  using UniPoly = carl::UnivariatePolynomial<Rational>;
  using MultiPoly = carl::MultivariatePolynomial<Rational>;
  using MultiCoeffUniPoly = carl::UnivariatePolynomial<MultiPoly>;
  using RAN = carl::RealAlgebraicNumber<Rational>;
  using RANPoint = carl::RealAlgebraicPoint<Rational>;
  using RANMap = std::map<carl::Variable, RAN>;
  using boost::optional;
  using boost::none;

  // Forward declarations
  struct Sector;
  std::ostream& operator<<(std::ostream& o, const Sector& s);

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
  std::ostream& operator<<(std::ostream& o, const OpenCell& c){
    o << "(cell (level " << c.size() << ") ";
    for(auto& sector : c){
      o << sector << " ";
    }
    return  o << ")";
  }

	/* using SampleLiftedWith = carl::Bitset; */
	/* using SampleRootOf = carl::Bitset; */
	/* using ConstraintSelection = carl::Bitset; */
	/* using OptionalPoly = boost::optional<const UPoly&>; */
	/* using OptionalID = boost::optional<std::size_t>; */
	/* using Assignment = std::map<carl::Variable, RAN>; */

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
     * TODO after plugging in a special point called alpha in [1].
     * TODO refactor out if section is usefull without cached point.
     */
    RAN cachedPoint;

    /**
     * Must be an irreducible poly of level k.
     * TODO explain design choice
     */
    /* MultiCoeffUniPoly poly; */
    MultiPoly poly;

  };

  std::ostream& operator<<(std::ostream& o, const Section& s) {
    return o << "(section " << s.poly << " " << s.cachedPoint << ")";
  }


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
    optional<Section> lowBound;

    optional<Section> highBound;

    bool isLowBoundNegInfty() const {
      return lowBound == none;
    }

    bool isHighBoundInfty() const {
      return highBound == none;
    }

  };

  std::ostream& operator<<(ostream& o, const Sector& s) {
    o << "(sector (low ";
    s.isLowBoundNegInfty() ? o << "-infty) " : o << s.lowBound.value() << ") " ;
    o << "(high ";
    s.isHighBoundInfty() ? o << "infty)" : o << s.highBound.value() << ")" ;
    return o << ")";
  }

  OpenCell createFullspaceCoveringCell(size_t level) {
    return OpenCell(level);
  }


  /**
   * Find the index of the highest variable (wrt. the ordering
   * in 'variableOrder') that occurs with positive degree in 'poly'.
   * Since levelOf is a math concept it starts counting at 1!
   * Examples:
   * - levelOf(2) == 0 wrt. any variable order
   * - levelOf(0*x+2) == 0 wrt. any variable order
   * - levelOf(x+2) == 1 wrt. [x < y < z]
   * - levelOf(x+2) == 2 wrt. [y < x < z]
   * - levelOf(x+2) == 3 wrt. [y < z < x]
   * - levelOf(x*y+2) == 2 wrt. [x < y < z] because of y
   * - levelOf(x*y+2) == 2 wrt. [y < x < z] because of x
   * - levelOf(x*y+2) == 3 wrt. [x < z < y] because of y
   * Preconditions:
   * - 'poly.gatherVariables()' must be a subset of 'variableOrder'.
   */
  size_t levelOf(const MultiPoly& poly,
      const std::vector<carl::Variable> variableOrder)
  {
    // 'gatherVariables()' collects only vars with positive degree
    std::set<carl::Variable> polyVarSet = poly.gatherVariables();
    // Algorithm:
    // Iterate through each variable inside 'variableOrder' in ascending order
    // and remove it from 'polyVarSet'. The last variable in 'polyVarSet' before
    // it becomes empty is the highest appearing variable in 'poly'.

    if(polyVarSet.empty())
      return 0; // for const-polys like '2'

    int level = 1;
    for(const auto& var : variableOrder) {
      polyVarSet.erase(var);
      // Last variable before 'polyVars' becomes empty is the highest variable.
      if(polyVarSet.empty()) {
        return level;
      }
      level++;
    }
    assert(false); // Should never be reached
    return 0;
  }

  /**
   * Merge the given open OpenCell 'cell' that contains the given 'point'
   * (called "alpha" in the paper) with a polynomial 'poly'.
   * Before the merge 'cell' represents a region that is sign-invariant
   * on other (previously merged) polynomials (all signs are non-zero).
   * The returned cell represents a region that is additionally sign-invariant on
   * 'poly' (also with non-zero sign).
   * @return either a OpenCell or nothing (representing a failed construction)
   */
  optional<OpenCell> mergeCellWithPoly(
    OpenCell& cell,
    const RANPoint& point,
    const std::vector<carl::Variable> variableOrder,
    const MultiPoly poly)
	{
    SMTRAT_LOG_INFO("smtrat.opencad", "Merge poly" << poly);
    assert(!poly.isZero());
    size_t level = levelOf(poly,variableOrder);
    // level for first variable starts at 1, but need it as index to start at 0.
    size_t levelIdx = level-1;
    SMTRAT_LOG_DEBUG("smtrat.opencad", "At level " << level << " merge it with " << cell);
    if(level == 0) // We have a non-zero, constant-poly, so no roots and nothing to do
      return optional<OpenCell>(cell);


    std::vector<carl::Variable> variableOrder4Lvl(level);
    std::copy_n(variableOrder.begin(),level,variableOrder4Lvl.begin());
    // Plug in all points into 'poly' and check if its zero.
    // This merge function is only correct for a full-dimensional CADCells,
    // i.e. the 'point' is not allowed to be a root of 'poly'
    // since this implies a lower-dimensional cell.
    // Use this special eval function because we plug in algebraic reals into the poly.
    RAN result = carl::RealAlgebraicNumberEvaluation::evaluate(poly,
      point.prefix(level),
      variableOrder4Lvl
    );
    if(result.isZero()) {
      SMTRAT_LOG_WARN("smtrat.opencad", "Poly vanished at point.");
      return none;
    }

		optional<OpenCell> newCell(cell);
    carl::Variable mainVariable = variableOrder[levelIdx];
    SMTRAT_LOG_TRACE("smtrat.opencad", "Current level variable: " << mainVariable);
    MultiCoeffUniPoly polyAsUnivar = poly.toUnivariatePolynomial(mainVariable);
		if (level > 1) {
      SMTRAT_LOG_INFO("smtrat.opencad", "Do Open-McCallum projection of this poly into level " << level - 1);
      // The "Open-McCallum projection" (called 'F' in [1]) of the to-be-merged
      // polys.
      std::vector<MultiPoly> projectionPolys;
      // Add leading coefficient and discriminant
      projectionPolys.emplace_back(polyAsUnivar.lcoeff());
      projectionPolys.emplace_back(MultiPoly(polyAsUnivar.discriminant()));
      SMTRAT_LOG_TRACE("smtrat.opencad", "Add leading coeff: " << polyAsUnivar.lcoeff());
      SMTRAT_LOG_TRACE("smtrat.opencad", "Add discriminant: " << polyAsUnivar.discriminant());


      Sector& currentSector = (*newCell)[levelIdx]; // Called D[k] in [1]
      // Add resultant of poly and lower sector bound
      if (!currentSector.isLowBoundNegInfty()) {
        MultiCoeffUniPoly resultant = (currentSector.lowBound->poly
          .toUnivariatePolynomial(mainVariable).resultant(polyAsUnivar));
        projectionPolys.push_back(MultiPoly(resultant));
        SMTRAT_LOG_TRACE("smtrat.opencad", "Add resultant with cell's low bound: " << resultant);
      }

      // Add resultant of poly and higher sector bound
      if (!currentSector.isHighBoundInfty()) {
        MultiCoeffUniPoly resultant = currentSector.highBound->poly
          .toUnivariatePolynomial(mainVariable).resultant(polyAsUnivar);
        projectionPolys.push_back(MultiPoly(resultant));
        SMTRAT_LOG_TRACE("smtrat.opencad", "Add resultant with cell's high bound: " << resultant);
      }
      SMTRAT_LOG_DEBUG("smtrat.opencad", "Projection result: " << projectionPolys);
      SMTRAT_LOG_INFO("smtrat.opencad", "Projection complete. Merge into cell");

      // Each poly in 'projectionPolys' must be factorized into its irreducible
      // factors.
      // Design decision: We use the CoCoA library as it seems to be
      // the fastest and most reliable library. Thus we need to enable
      // carl::cocoa in carl ccmake. Note that CoCoA needs to know the variable
      // names of the polynomials in every computation. The stateful
      // 'CoCoaAdaptor' and its constructor take care of that.
      carl::CoCoAAdaptor<MultiPoly> cocoaLib(projectionPolys);
      for(const MultiPoly& projPoly : projectionPolys) {
        // Constant factors are irrelevant for root computations, so leave them out.
        const bool keepConstFactorsFlag = false;
        for(const auto& factorAndSomeInt:
            cocoaLib.factorize(projPoly, keepConstFactorsFlag))
        {
          SMTRAT_LOG_DEBUG("smtrat.opencad", "Merge irreducible factor: " << factorAndSomeInt.first);
          if(!(newCell = mergeCellWithPoly(
                *newCell,
                point,
                variableOrder,
                factorAndSomeInt.first)))
          {
            // If submerge fails, this merge fails too
            return none;
          }
        }
      }
    }

    std::map<carl::Variable, RAN> pointAsMap;
    for(int i = 0; i < level-1; i++)
      pointAsMap[variableOrder[i]] = point[i];

		// Isolate real roots of level-k 'poly' after plugin in a level-(k-1) point.
    // level is >= 1
    RAN point_k = point[levelIdx]; // called alpha_k in [1]
    SMTRAT_LOG_INFO("smtrat.opencad", "Continue at level " << level << ". Search closest bounds to " << point_k);
    // It must be ensured that poly does not vanish under this point!
    std::vector<RAN> roots
      = *carl::rootfinder::realRoots(polyAsUnivar, pointAsMap);
    if(roots.empty()) {
      SMTRAT_LOG_INFO("smtrat.opencad", "No bound candidates");
      return newCell;
    }

    std::sort(roots.begin(), roots.end());
    SMTRAT_LOG_DEBUG("smtrat.opencad", "Bound candidates: " << roots);
    Sector& currentSector = (*newCell)[levelIdx]; // Called D[k] in [1]
    SMTRAT_LOG_DEBUG("smtrat.opencad", "Bounds before: " << currentSector);

    // Search for closest roots to point_k, i.e.
    // someRoot ... < root_lower < point_k < root_higher < ... someOtherRoot
    auto root_higher = std::find_if(
        roots.begin(),
        roots.end(),
        [&point_k] (const RAN& otherPoint) { return otherPoint > point_k; });
    assert(root_higher == roots.end() || *root_higher != point_k);
    // Update high bound if a tighter root is found s.t.
    // point_k < root_higher < cell_highBound
    if(root_higher != roots.end() &&
        ( currentSector.isHighBoundInfty() ||
          *root_higher < currentSector.highBound->cachedPoint)) {
      currentSector.highBound = Section {*root_higher, poly};
    }

    // Update low bound if a tighter root is found s.t.
    // cell_lowBound < root_lower < point_k
    if(root_higher != roots.begin()) {
      auto root_lower = --root_higher;
      assert(*root_lower != point_k);
      if( currentSector.isLowBoundNegInfty() ||
        *root_lower > currentSector.lowBound->cachedPoint)
      {
        currentSector.lowBound = Section {*root_lower, poly};
      }
    }
    SMTRAT_LOG_DEBUG("smtrat.opencad", "Bounds after: " << currentSector);
    return newCell;
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
  optional<OpenCell> createBrownOpenOneCell(
    const std::vector<MultiPoly> polySet,
    const RANPoint& point,
    const std::vector<carl::Variable>& variableOrder)
  {
		// Note that combining 'variableOrder' and 'point' into
		// a single object like Variable-to-RAN-map
		// is bad because a map may rearrange the variables and destroy
    // any desired variable ordering.
    assert(variableOrder.size() == point.dim());
    SMTRAT_LOG_INFO("smtrat.opencad", "Create BrownOpenOneCell");
    SMTRAT_LOG_DEBUG("smtrat.opencad", "Use point " << point << " wrt. variable order " << variableOrder);

    optional<OpenCell> cell = createFullspaceCoveringCell(point.dim());
    for(const auto& poly : polySet){
      SMTRAT_LOG_INFO("smtrat.opencad", "Merge input poly");
      SMTRAT_LOG_DEBUG("smtrat.opencad", "Input poly: " << poly);
      if (! (cell = mergeCellWithPoly(*cell, point, variableOrder, poly))) {
        // If any merge fails, this whole construction fails too
        SMTRAT_LOG_WARN("smtrat.opencad", "Construction failed");
        return none;
      }
    }
    SMTRAT_LOG_DEBUG("smtrat.opencad", "Final cell: " << cell.value());
    return cell;
  }

} // namespace onecellcad
} // namespace smtrat
