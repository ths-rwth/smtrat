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
#include <experimental/optional>
/* #include <boost/optional.hpp> */

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

namespace onecellcad {

  using UniPoly = carl::UnivariatePolynomial<Rational>;
  using MultiPoly = carl::MultivariatePolynomial<Rational>;
  using MultiCoeffUniPoly = carl::UnivariatePolynomial<MultiPoly>;
  using RAN = carl::RealAlgebraicNumber<Rational>;
  using RANPoint = carl::RealAlgebraicPoint<Rational>;
  using RANMap = std::map<carl::Variable, RAN>;
  /* using boost::optional; */
  /* using boost::none; */

  /**
   * Represent a cell's closed-interval-boundary along one single axis by an
   * irreducible, multivariate poly of level k.
   * A section is an algebraic/"moving" boundary, because it's basically a
   * function f: algReal^{k-1} -> algReal; from a multi-dimensional input point
   * of level k-1 (whose components are algebraic reals) to an algebraic real
   * (the bound along k-th axis that changes depending on the input point).
   */
  using Section = MultiPoly;
  struct Section {
    MultiPoly poly;

    /**
     * A single, special bound after having plugged a specific point of level k-1
     * can be cached for performance (needed for [1]).
     */
    RAN cachedPoint;
  }

  std::ostream& operator<<(std::ostream& o, const Section& s) {
    return o << "(section " << s.poly << " " << s.cachedPoint << ")";
  }

  /**
   * Represent a cell's open-interval-boundary along one single axis by two
   * irreducible, multivariate polys of level k.
   * A sector is an algebraic/"moving" boundary, because it's basically a
   * function f: algReal^{k-1} -> (algReal,algReal); from a multi-dimensional
   * input point of level k-1 (whose components are algebraic reals) to a pair
   * of algebraic reals (the lower and upper bound for an open interval along
   * k-th axis that changes depending on the input point).
   * Note that if 'lowBound' or 'highBound' is not defined, then this
   * represents negative and positive infinity, respectively.
   */
  struct Sector {
    std::optional<Section> lowBound;

    std::optional<Section> highBound;

    bool isLowBoundNegInfty() const {
      return lowBound == std::none;
    }

    bool isHighBoundInfty() const {
      return highBound == std::none;
    }

  };

  std::ostream& operator<<(ostream& o, const Sector& s) {
    o << "(sector (low ";
    s.isLowBoundNegInfty() ? o << "-infty) " : o << s.lowBound.value() << ") " ;
    o << "(high ";
    s.isHighBoundInfty() ? o << "infty)" : o << s.highBound.value() << ")" ;
    return o << ")";
  }

  /**
   * Represent a single open cell [1].
   * A cell is a collection of boundary objects along each axis.
   * In case of an open cell, the boundary objects are all sectors.
   */
  using OpenCell = std::vector<Sector>;

  std::ostream& operator<<(std::ostream& o, const OpenCell& c){
    o << "(cell (level " << c.size() << ") ";
    for(auto& sector : c){
      o << sector << " ";
    }
    return  o << ")";
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
   * (called "alpha" in [1]) with a polynomial 'poly'.
   * Before the merge 'cell' represents a region that is sign-invariant
   * on other (previously merged) polynomials (all signs are non-zero).
   * The returned cell represents a region that is additionally sign-invariant on
   * 'poly' (also with non-zero sign).
   * @return either an OpenCell or nothing (representing a failed construction)
   */
  std::optional<OpenCell> mergeCellWithPoly(
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
      return std::optional<OpenCell>(cell);


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
      return std::none;
    }

    std::optional<OpenCell> newCell(cell);
    carl::Variable mainVariable = variableOrder[levelIdx];
    SMTRAT_LOG_TRACE("smtrat.opencad", "Current level variable: " << mainVariable);
    MultiCoeffUniPoly polyAsUnivar = poly.toUnivariatePolynomial(mainVariable);
		if (level > 1) {
      SMTRAT_LOG_INFO("smtrat.opencad", "Do Open-McCallum projection of this poly into level " << level - 1);
      std::vector<MultiPoly> projectionPolys(4)
        .emplace_back(polyAsUnivar.lcoeff());
        .emplace_back(MultiPoly(polyAsUnivar.discriminant()));
      SMTRAT_LOG_TRACE("smtrat.opencad", "Add leading coeff: " << polyAsUnivar.lcoeff());
      SMTRAT_LOG_TRACE("smtrat.opencad", "Add discriminant: " << polyAsUnivar.discriminant());


      Sector& sectorAtLvl = (*newCell)[levelIdx];
      // Add resultant of poly and lower sector bound
      if (!sectorAtLvl.isLowBoundNegInfty()) {
        projectionPolys.emplace_back(MultiPoly(
          sectorAtLvl.lowBound->poly
            .toUnivariatePolynomial(mainVariable)
            .resultant(polyAsUnivar)));
        SMTRAT_LOG_TRACE("smtrat.opencad", "Add resultant with cell's low bound: " << resultant);
      }

      // Add resultant of poly and higher sector bound
      if (!sectorAtLvl.isHighBoundInfty()) {
        MultiCoeffUniPoly resultant = sectorAtLvl.highBound->poly
          .toUnivariatePolynomial(mainVariable).resultant(polyAsUnivar);
        projectionPolys.push_back(MultiPoly(resultant));
        SMTRAT_LOG_TRACE("smtrat.opencad", "Add resultant with cell's high bound: " << resultant);
      }
      SMTRAT_LOG_DEBUG("smtrat.opencad", "Projection result: " << projectionPolys);
      SMTRAT_LOG_INFO("smtrat.opencad", "Projection complete. Merge into cell");

      // Each poly in 'projectionPolys' must be factorized into its irreducible
      // factors.
      for(const MultiPoly& factor :
            carl::CoCoAAdatpro<MultiPoly>(projectionPolys)
              .irreducibleFactors(projectionPolys))
      {
        SMTRAT_LOG_DEBUG("smtrat.opencad", "Merge irreducible factor: " << factorAndSomeInt.first);
        if(!(newCell = mergeCellWithPoly(
              *newCell,
              point,
              variableOrder,
              factor)))
        {
          // If submerge fails, this merge fails too
          return std::none;
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
    Sector& sectorAtLvl = (*newCell)[levelIdx]; // Called D[k] in [1]
    SMTRAT_LOG_DEBUG("smtrat.opencad", "Bounds before: " << sectorAtLvl);

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
        ( sectorAtLvl.isHighBoundInfty() ||
          *root_higher < sectorAtLvl.highBound->cachedPoint)) {
      sectorAtLvl.highBound = Section {*root_higher, poly};
    }

    // Update low bound if a tighter root is found s.t.
    // cell_lowBound < root_lower < point_k
    if(root_higher != roots.begin()) {
      auto root_lower = --root_higher;
      assert(*root_lower != point_k);
      if( sectorAtLvl.isLowBoundNegInfty() ||
        *root_lower > sectorAtLvl.lowBound->cachedPoint)
      {
        sectorAtLvl.lowBound = Section {*root_lower, poly};
      }
    }
    SMTRAT_LOG_DEBUG("smtrat.opencad", "Bounds after: " << sectorAtLvl);
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
  std::optional<OpenCell> createBrownOpenOneCell(
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

    std::optional<OpenCell> cell = createFullspaceCoveringCell(point.dim());
    for(const auto& poly : polySet){
      SMTRAT_LOG_INFO("smtrat.opencad", "Merge input poly");
      SMTRAT_LOG_DEBUG("smtrat.opencad", "Input poly: " << poly);
      if (! (cell = mergeCellWithPoly(*cell, point, variableOrder, poly))) {
        // If any merge fails, this whole construction fails too
        SMTRAT_LOG_WARN("smtrat.opencad", "Construction failed");
        return std::none;
      }
    }
    SMTRAT_LOG_DEBUG("smtrat.opencad", "Final cell: " << cell.value());
    return cell;
  }

} // namespace onecellcad
} // namespace smtrat
