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
 * [2] McCallum .. something about well-oriented
 */

#include <vector>
#include <unordered_map>
#include <set>
#include <algorithm>
#include <experimental/optional> // remove when c++17 available
/* #include <optional> // uncomment when c++17 is available*/

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
#include "variant.hpp" // Workaround; remove when c++17 available
#include "Assertables.h"

namespace smtrat {
namespace onecellcad {

  using UniPoly = carl::UnivariatePolynomial<smtrat::Rational>;
  using MultiPoly = carl::MultivariatePolynomial<smtrat::Rational>;
  using MultiCoeffUniPoly = carl::UnivariatePolynomial<MultiPoly>;
  using RAN = carl::RealAlgebraicNumber<smtrat::Rational>;
  using RANPoint = carl::RealAlgebraicPoint<smtrat::Rational>;
  using RANMap = std::map<carl::Variable, RAN>;
  using std::experimental::optional;
  using std::experimental::nullopt;

  enum class PolyTag = {ORDER_INVARIANT, SIGN_INVARIANT};

  enum class ShrinkResult = {SUCCESS, FAIL};

  struct TaggedPoly {
    PolyTag tag;

    MultiPoly poly;

    /** We cache the poly's level for performance. */
    std::size_t level;
  };

  std::ostream& operator<<(std::ostream& o, const TaggedPoly& s) {
    return o << "(tag " << p.tag << " poly " << p.poly << ")";
  }


  /**
   * Represent a cell's closed-interval-boundary object along one single axis by an
   * irreducible, multivariate polynomial of level k.
   * A section is an algebraic/"moving" boundary, because it's basically a
   * function f: algReal^{k-1} -> algReal; from a multi-dimensional input point
   * of level k-1 (whose components are algebraic reals) to an algebraic real
   * (the bound along k-th axis that changes depending on the input point).
   */
  struct Section {
    // A section is always finite, a sector may have infty bounds!
    MultiPoly poly;

    RAN cachedPoint;
  };

  std::ostream& operator<<(std::ostream& o, const Section& s) {
    return o << "(section " << s.poly << " " << s.cachedPoint << ")";
  }

  /**
   * Represent a cell's open-interval boundary object along one single axis by two
   * irreducible, multivariate polynomials of level k.
   * A sector is an algebraic/"moving" boundary, because it's basically a
   * function f: algReal^{k-1} -> (algReal,algReal); from a multi-dimensional
   * input point of level k-1 (whose components are algebraic reals) to a pair
   * of algebraic reals (the lower and upper bound for an open interval along
   * k-th axis that changes depending on the input point).
   * Note that if 'lowBound' or 'highBound' is not defined, then this
   * represents negative and positive infinity, respectively.
   */
  struct Sector {
    /** A std::nullopt lowBound represents negative infinity */
    std::optional<Section> lowBound;

    /** A std:nullopt highBound represents infinity */
    std::optional<Section> highBound;
  };

  /* std::ostream& operator<<(ostream& o, const Sector& s) { */
  /*   o << "(sector (low "; */
  /*   s.isLowBoundNegInfty() ? o << "-infty) " : o << s.lowBound.value() << ") " ; */
  /*   o << "(high "; */
  /*   s.isHighBoundInfty() ? o << "infty)" : o << s.highBound.value() << ")" ; */
  /*   return o << ")"; */
  /* } */

  /**
   * Represent a single cell [1].
   * A cell is a collection of boundary objects along each axis, called
   * cell-components based on math. vectors and their components.
   */
  using CADCell = std::vector<std::variant<Sector, Section>>;

  /**
   * @return Dimension of a hybercube to which the given cell is homeomorphic,
   * i.e., count the number of sectors of the given Cell restricted to its first
   * components (with index 0 to 'uptoLevel').
   */
  std::size_t cellDimension(const CADCell& cell, const std::size_t uptoLevel = cell.size()-1) {
    std::size_t sectorCount = 0;
    for(auto& boundComponent : cell) {
    for(std::size_t i = 0; i <= uptoLevel; i++) {
      auto& boundComponent = cell[i];
      if (std::holds_alternative<Sector>(boundComponent))
        sectorCount++;
    }
    return sectorCount;
  }


  /**
   * Group static information like point and variable order
   * as well as dynamic information like projection polys and delineating polys, created during
   * construction, that are necessary for merging the next polynomial.
   */
  struct ShrinkContext {
    const RANPoint point;

    const std::vector<carl::Variable> variableOrder;

    /** The CoCoAAdaptor transforms variables into an internal format that we want have done only once
     * and cached. */
    const carl::CoCoAAdaptor<MultiPoly> factorizer;
  };


  /**
   * Store all processed polys.
   */
  struct PolyLog {
    /** This collection is called "P_prj" in [1] */
    std::vector<TaggedPoly> projectionPolys;

    /** Only delinating polys. This collection is called "P_dln" in [1] */
    std::vector<TaggedPoly> delineators;
  };

  /**
   * Represent a merge failure explanation.
   */
  struct CellConstructFail {
    /** Unmergeable poly, that vanishes over positive-dimensional cell */
    MultiPoly witness;

    CADCell lastRefinedPositiveDimCell;
  };


  /* std::ostream& operator<<(std::ostream& o, const OpenCADCell& c){ */
  /*   o << "(cell (level " << c.size() << ") "; */
  /*   for(auto& sector : c){ */
  /*     o << sector << " "; */
  /*   } */
  /*   return  o << ")"; */
  /* } */

  CADCell buildFullspaceCoveringCell(std::size_t cellComponentCount) {
    return CADCell(cellComponentCount);
  }


  /**
   * Find the index of the highest variable (wrt. the ordering
   * in 'variableOrder') that occurs with positive degree in 'poly'.
   * Although 'level' is a math concept that starts counting at 1
   * we start counting at 0 and represent "no level/variable" as std::nullopt
   * because it simplifies using the level directly as an index in arrays
   * or vectors.
   * Examples: TODO update exampels
   * - polyLevel(2) == 0 wrt. any variable order
   * - polyLevel(0*x+2) == 0 wrt. any variable order
   * - polyLevel(x+2) == 1 wrt. [x < y < z]
   * - polyLevel(x+2) == 2 wrt. [y < x < z]
   * - polyLevel(x+2) == 3 wrt. [y < z < x]
   * - polyLevel(x*y+2) == 2 wrt. [x < y < z] because of y
   * - polyLevel(x*y+2) == 2 wrt. [y < x < z] because of x
   * - polyLevel(x*y+2) == 3 wrt. [x < z < y] because of y
   * Preconditions:
   * - 'poly.gatherVariables()' must be a subset of 'variableOrder'.
   */
  std::optional<std::size_t> polyLevel(
      const std::vector<carl::Variable>& variableOrder,
      const MultiPoly& poly)
  {
    // precondition:
    assert(isSubset(poly.gatherVariables(), variableOrder));

    // Algorithm:
    // Iterate through each variable inside 'variableOrder' in ascending order
    // and remove it from 'polyVariables'. The last variable in 'polyVariables' before
    // it becomes empty is the highest appearing variable in 'poly'.

    // 'gatherVariables()' collects only variables with positive degree
    std::set<carl::Variable> polyVariables = poly.gatherVariables();

    if(polyVariables.empty())
      return std::nullopt; // for const-polys like '2'

    //TODO use indexed for-loop now
    std::size_t level = 0;
    for(const auto& var : variableOrder) {
      polyVariables.erase(var);
      // Last variable before 'polyVariables' becomes empty is the highest variable.
      if(polyVariables.empty())
        return level;

      level++;
    }

    assert(false); // should be unreachable
    return std::nullopt;
  }

  /**
   * Create a mapping from the first variables (with index 0 to 'level') in the
   * given 'variableOrder' to the first components of the given 'point'.
   */
  std::map<carl::Variable, RAN> toStdMap(
      const std::vector<carl::Variable>& variableOrder,
      const std::size_t level,
      const RANPoint& point)
  {
    std::map<carl::Variable, RAN> varToRANMap;
    for(std::size_t i = 0; i <= level; i++)
      varToRANMap[variableOrder[i]] = point[i];
    return varToRANMap;
  }

  inline
  bool contains(const std::vector<TaggedPoly>& polys, const MultiPoly& poly) {
    auto isMatch = [&poly] (const TaggedPoly& taggedPoly) {
      return taggedPoly.poly == poly
    };
    return std::find_if(polys.begin(), polys.end(), isMatch) != polys.end();
  }

  inline
  bool contains(const std::vector<TaggedPoly>& polys, const Tagged& poly) {
    return std::find(polys.begin(), polys.end(), poly) != polys.end();
  }

  bool isAlreadyProcessed(const PolyLog& log, const TaggedPoly& poly) {
    // matches if poly is found with its tag or an oi-tag
    auto isMatch = [&poly] (const TaggedPoly& processedPoly) {
      return processedPoly.poly == poly.poly &&
        (processedPoly.tag == poly.tag
          || processedPoly.tag == PolyTag::ORDER_INVARIANT);
    };
    if (std::find_if(log.projectionPolys.begin(), log.projectionPolys.end(), isMatch)
      != log.projectionPolys.end())
      return true;

    return std::find_if(log.delineators.begin(), log.delineators.end(), isMatch)
      != log.delineators.end();
  }

  /**
   * Check if an n-variate 'poly' p(x1,..,xn) already becomes the zero poly
   * after plugging in p(a1,..,an-1, xn), where a1,..an-1 are the first n-1
   * algebraic real components from 'point'.
   */
  inline
  bool vanishesEarly(
      const std::vector<carl::Variable>& variableOrder,
      const RANPoint& point,
      const TaggedPoly& poly)
  {
    auto resultPoly =
      carl::RealAlgebraicNumberEvaluation::evaluateCoefficients(
        poly.poly.toUnivariatePolynomial(variableOrder[poly.level]),
        toStdMap(variableOrder, poly.level-1, point),
        {});
    return resultPoly.isZero();
  }

  inline
  bool isPointRootOfPoly(
      const std::vector<carl::Variable>& variableOrder,
      const RANPoint& point,
      const TaggedPoly& poly)
  {
    return isPointRootOfPoly(variableOrder, point, poly.level, poly.poly);
  }

  bool isPointRootOfPoly(
      const std::vector<carl::Variable>& variableOrder,
      const RANPoint& point,
      const std::size_t polyLevel,
      const MultiPoly& poly)
  {
    const std::size_t componentCount = polyLevel+1;
    std::vector<carl::Variable> subVariableOrder;
    subVariableOrder.reserve(componentCount);
    std::copy_n(variableOrder.begin(), componentCount, subVariableOrder.begin());
    // 'evaluate' only accepts a point and variables with exactly
    // 'componentCount' number of components
    RAN result = carl::RealAlgebraicNumberEvaluation::evaluate(
      poly,
      point.subpoint(componentCount),
      subVariableOrder
    );
    return result.isZero();
  }

  bool isPointInsideCell(
      const std::vector<carl::Variable>& variableOrder,
      const const RANPoint& point,
      const Cell& cell)
  {
    // precondition
    assert(point.dim() >= 1);
    assert(cell.size() <= point.dim());

    for (std::size_t level = 0; level < point.dim(); level++) {
      if (std::holds_alternative<Section>(cell[level])) {
        const Sector sector = std::get<Sector>(cell[level]);
        if (!isPointRootOfPoly(variableOrder, point, level, sector.poly))
          return false;
        if (sector.cachedPoint != point[level])
          return false;
      } else {
        const Section section = std::get<Section>(cell[level]);
        if (section.highBound) {
          const Sector highBound = *section.highBound;
          if (point[level] > highBound.cachedPoint)
            return false;
          if (!isSubset(
                {highBound.cachedPoint},
                allLastVariableRoots(variableOrder, point, highBound.poly, level)))
          {
            return false;
          }
        }
        if (section.lowBound) {
          const Sector lowBound = *section.lowBound;
          if (point[level] < lowBound.cachedPoint)
            return false;
          if (!isSubset(
                {lowBound.cachedPoint},
                allLastVariableRoots(variableOrder, point, lowBound.poly, level)))
          {
            return false;
          }
        }
      }
    }
      return true;
  }

  /**
   * Given a poly p(x1,..,xn), return all roots of the univariate poly
   * p(a1,..,an-1, xn), where a1,..an-1 are the first algebraic real components
   * from 'point'.
   */
  std::vector<RAN> allLastVariableRoots(
      const std::vector<carl::Variable>& variableOrder,
      const RANPoint& point,
      const MultiPoly& poly,
      const std::size_t polyLevel)
  {
    // 'realRoots' returns std::nullopt if poly vanishes
    // early, but here we don't care
    auto rootsOpt = carl::rootfinder::realRoots(
      poly.toUnivariatePolynomial(),
      toStdMap(variableOrder, polyLevel-1, point));
    if (rootsOpt)
      return *rootsOpt;
    else
      return {};
  }


  /**
   * Shrink the component of the 'cell' at the 'boundCandidate's level around
   * the given point if the 'boundCandidate' is a tighter bound.  Don't
   * recursively shrink lower level components of the cell.
   * Note that a cell's sector may collapse into a section, which is why we
   * need to pass in a cell and not only its sector.
   * Note that this shrink function is always "successful", even if the cell
   * was not shrunk.
   * @param boundCandidate Must be a non-const irreducible polynomial that does
   * not vanish early.
   */
  void shrinkSingleComponent(
    const ShrinkContext& ctx,
    const TaggedPoly& boundCandidate,
    Cell& cell)
  {
    // This function is called "Update" in [1]
    // precondition:
    assert(isNonConstantIrreducible(boundCandidate.poly));
    assert(!vanishesEarly(ctx.variableOrder, point, boundCandidate));

    if (std::get<Section>(cell[boundCandidate.level]))
      return; // canot shrink further

    Sector& sectorAtLvl = std::get<Sector>(cell[boundCandidate.level]);
    RAN value = ctx.point[boundCandidate.level]; // called alpha_k in [1]
    SMTRAT_LOG_INFO("smtrat.onecellcad", "Continue at level " << boundCandidate.level
        << ". Search closest bounds to " << value);
    // Isolate real roots of level-k 'poly' after plugin in a level-(k-1) point.
    // Poly must not vanish under this subpoint!
    std::vector<RAN> roots =
      allLastVariableRoots(ctx.variableOrder, boundCandidate, boundCandidate.level, ctx.point);
    if(roots.empty()) {
      SMTRAT_LOG_INFO("smtrat.onecellcad", "No boundPoint candidates");
      return;
    }
    SMTRAT_LOG_DEBUG("smtrat.onecellcad", "BoundPoint candidates: " << roots);
    SMTRAT_LOG_DEBUG("smtrat.onecellcad", "Bounds before: " << sectorAtLvl);

    // Search for closest roots/boundPoints to value, i.e.
    // someRoot ... < closestLower <= value <= closestUpper < ... someOtherRoot
    std::optional<RAN> closestLower;
    std::optional<RAN> closestUpper;
    for (const auto& boundPointCandidate: roots) {
      if (boundPointCandidate < value) {
        if (!closestLower || *closestLower < boundPointCandidate)
          closestLower = boundPointCandidate;
      } else if (boundPointCandidate == value) {
        // Sector collapses into a section
        cell[boundCandidate.level] = Section{boundPointCandidate.poly, boundPointCandidate};
        SMTRAT_LOG_DEBUG("smtrat.onecellcad", "Bounds after: " << cell[boundCandidate.level]);
        return;
      } else { // value < boundPointCandidate
        if (!closestUpper || boundPointCandidate < *closestUpper)
          closestUpper = boundPointCandidate;
      }
    }

    // Sector is still a sector
    if (closestLower)
      sectorAtLvl.lowBound = {boundPointCandidate.poly, *closestLower};

    if (closestUpper)
      sectorAtLvl.highBound = {boundPointCandidate.poly, *closestUpper};

    SMTRAT_LOG_DEBUG("smtrat.onecellcad", "Bounds after: " << sectorAtLvl);
  }

  /**
   * Find the smallest index m such that in the set S of all m-th partial
   * derivatives of the given poly, such that there is a derivative that does
   * not vanish early [1].
   * Note that m > 0 i.e, this function never just returns the given poly,
   * which is the 0th partial derivative of itself.
   * @param poly must not be a const-poly like 2, otherwise this function
   * does not terminate.
   * @return Actually only returns the set S
   */
  std::vector<MultiPoly> partialDerivativesLayerWithSomeNonEarlyVanishingPoly(
    const std::vector<carl::Variable>& variableOrder,
    const RANPoint& point,
    const TaggedPoly& mainPoly)
  {
    assert(!mainPoly.poly.isConstant());
    // We search for this set of partial derivatives "layer by layer".
    // The layer of 0-th partial derivatives is the mainPoly itself.
    std::vector<MultiPoly> layerOfDerivates;
    layerOfDerivates.emplace_back(mainPoly.poly);
    bool foundSomeNonEarlyVanishingDerivative = false;

    do {
      std::vector<MultiPoly> nextLayer;
      for (const auto& poly : layerOfDerivates) {
        // Derive poly wrt to each variable (up to 'boundCandidate.level')
        for (std::size_t varIdx = 0; varIdx <= boundCandidate.level; varIdx++) {
          const auto derivative = poly.derivative(ctx.variableOrder[varIdx]);
          if (derivative.isZero())
            continue;
          nextLayer.emplace_back(derivative);
          if (foundSomeNonEarlyVanishingDerivative)
            continue; // avoid expensive vanishing check

          if (derivative.isConstant() ||
                !vanishesEarly(ctx.variableOrder, {poly, mainPoly.level}, , ctx.point))
            foundSomeNonEarlyVanishingDerivative = true;
            // still need to compute all remaining nextLayer-polys
          }
        }
      }
      layerOfDerivates = std::move(nextLayer);
    } while (!foundSomeNonEarlyVanishingDerivative);

    return layerOfDerivates;
  }

  ShrinkResult shrinkCellWithEarlyVanishingPoly(
    const ShrinkContext& ctx,
    PolyLog& polyLog,
    const TaggedPoly& boundCandidate,
    Cell& cell)
  {
    // This function is called MergeNull in [1]
    // precondition:
    assert(vanishesEarly(ctx.variableOrder, point, boundCandidate));
    assert(isNonConstantIrreducible(boundCandidate.poly));

    auto shrinkResult = refineNull(ctx, polyLog, boundCandidate.poly, boundCandidate.level, cell);
    if (shrinkResult == ShrinkResult::FAIL)
      return shrinkResult;

    if (boundCandidate.tag == PolyTag::SIGN_INVARIANT) {
      polyLog.projectionPolys.emplace_back(boundCandidate);
      return ShrinkResult::SUCCESS
    } else { //boundCandidate.tag == PolyTag::ORDER_INVARIANT
      if (cellDimension(cell, boundCandidate.level-1) > 0)
        return ShrinkResult::FAIL;

      // Construct a delineating poly as the sum of all non-earlyVanishing,
      // squared m-th partial derivatives.
      MultiPoly delineator; //start with zero
      for (const auto& poly :
            partialDerivativesLayerWithSomeNonEarlyVanishingPoly(
              ctx.variableOrder, ctx.point, boundCandidate))
      {
        if (!vanishesEarly(ctx.variableOrder, {poly, boundCandidate.level}, ctx.point))
          delineator += poly*poly;
      }

      if (!delineator.isConstant()) {
        const size_t delineatorLevel = polyLevel(delineator);
        shrinkSingleComponent(ctx, {delineator, delineatorLevel}, cell);

        const TaggedPoly taggedDelineator{
          PolyTag::ORDER_INVARIANT,
          delineator,
          delineatorLevel};
        polyLog.projectionPolys.emplace_back(taggedDelineator);
        polyLog.delineators.emplace_back(taggedDelineator);
      }
      return ShrinkResult::SUCCESS;
    }
  }

  /** Compute the resultant of two multivariate polynomials wrt. a given 'mainVariable' */
  inline
  MultiPoly resultant(const carl::Variable& mainVariable, const MultiPoly& p1, const MultiPoly& p2) {
    const auto p1UPoly = p1.toUnivariatePolynomial(mainVariable);
    const auto p2UPoly = p2.toUnivariatePolynomial(mainVariable);
    return MultiPoly(p1UPoly.resultant(p2UPoly));
  }

  inline
  MultiPoly discriminant(const carl::Variable& mainVariable, const MultiPoly& p) {
    return MultiPoly(p.toUnivariatePolynomial(mainVariable).discriminant());


  ShrinkResult shrinkCellWithIrreducibleFactorsOfPoly(
    const ShrinkContext& ctx,
    PolyLog& polyLog,
    const TaggedPoly& poly,
    Cell& cell)
  {
    for (const auto& factor : ctx.factorizer.irreducibleFactorsOf(poly.poly)) {
      SMTRAT_LOG_DEBUG("smtrat.onecellcad", "Merge irreducible factor: " << factor);
      if (factor.isConstant())
        continue;

      const std::size_t factorLevel = *polyLevel(factor, ctx.variableOrder);
      TaggedPoly factorWithInheritedTag = {poly.tag, factor, factorLevel};
      if (shrinkCell(ctx, polyLog, factorWithInheritedTag, cell)
            == ShrinkResult::FAIL)
      {
        SMTRAT_LOG_WARN("smtrat.onecellcad", "Construction failed");
        // If subCellshrinking fails, this shrinking fails too
        return ShrinkResult::FAIL;
      }
    }
  }

  ShrinkResult refineNonNull(
    const ShrinkContext& ctx,
    PolyLog& polyLog,
    const TaggedPoly& boundCandidate,
    Cell& cell)
  {
    // This function is called "RefNonNull" in [1]
    // precondition:
    assert(isNonConstantIrreducible(boundCandidate.poly));
    assert(!vanishesEarly(ctx.variableOrder, point, boundCandidate));

    const auto mainVariable = ctx.variableOrder[boundCandidate.level];
    const auto boundCandidateUniPoly =
        boundCandidate.poly.toUnivariatePolynomial(mainVariable);

    // Do early-exit tests:
    for (const auto& coeff : boundCandidateUniPoly.coefficients()) {
      if (coeff.isConstant() && !coeff.isZero())
        return ShrinkResult::SUCCESS;
    }

    const auto& leadCoeff = boundCandidate.poly.lcoeff(mainVariable);
    if ((contains(polyLog.projectionPolys, leadCoeff)
         || contains(polyLog.delineators, leadCoeff))
        && !isPointRootOfPoly(ctx.variableOrder, ctx.point, *polyLevel(leadCoeff), leadCoeff))
    {
      return ShrinkResult::SUCCESS;
    }

    const auto discriminant = discriminant(mainVariable, boundCandidate.poly);
    if ((contains(polyLog.projectionPolys, discriminant)
         || contains(polyLog.delineators, discriminant))
        && !isPointRootOfPoly(ctx.variableOrder, ctx.point, *polyLevel(discriminant), discriminant))
    {
      return ShrinkResult::SUCCESS;
    }

    // optional early-exit check: if for every point in subcell, poly does not
    // vanish, return success. No idea how.

    for (const auto& coeff : boundCandidateUniPoly.coefficients()) {
      // find first non-vanishing coefficient:
      const std::size_t coeffLevel = *polyLevel(coeff); // certainly non-constant
      if (!isPointRootOfPoly(ctx.variableOrder, ctx.point, coeffLevel, coeff)) {
        return
          shrinkCellWithIrreducibleFactorsOfPoly(
            ctx,
            polyLog,
            {PolyTag::SIGN_INVARIANT, coeff, coeffLevel},
            cell);
      }
    }
    return ShrinkResult::SUCCESS;
  }


  ShrinkResult refineNull(
    const ShrinkContext& ctx,
    PolyLog& polyLog,
    const TaggedPoly& boundCandidate,
    Cell& cell)
  {
    // This function is called "RefNull" in [1]
    // precondition:
    assert(isNonConstantIrreducible(boundCandidate.poly));
    assert(isPointRootOfPoly(ctx.variableOrder, point, boundCandidate));
    const auto mainVariable = ctx.variableOrder[boundCandidate.level];
    const auto boundCandidateUniPoly =
        boundCandidate.poly.toUnivariatePolynomial(mainVariable);
    std::vector<TaggedPoly> projectionResult;

    projectionResult.emplace_back({
      PolyTag::ORDER_INVARIANT,
      discriminant(mainVariable, boundCandidate.poly),
      0}); // hack: we compute the level later in this function

    projectionResult.emplace_back({
      PolyTag::ORDER_INVARIANT,
      boundCandidateUniPoly.lcoeff(),
      0}); // hack: we compute the level later in this function

    projectionResult.emplace_back({
      PolyTag::ORDER_INVARIANT,
      boundCandidateUniPoly.tcoeff(),
      0}); // hack: we compute the level later in this function

    for (const auto& resultPoly : projectionResult) {
      if (resultPoly.isConstant())
        continue;

      // Hack: add the correct level here
      resultPoly = *polyLevel(ctx.variableOrder, resultPoly);
      if (shrinkCellWithIrreducibleFactorsOfPoly(ctx, polyLog, resultPoly, cell)
            == ShrinkResult::FAIL)
        return ShrinkResult::FAIL;
    }

    return ShrinkResult::SUCCESS;
  }


  ShrinkResult shrinkCellWithPolyHavingPointAsRoot(
    const ShrinkContext& ctx,
    PolyLog& polyLog,
    const TaggedPoly& boundCandidate,
    Cell& cell)
  {
    // This function is called MergeRoot in [1]
    // precondition:
    assert(!vanishesEarly(ctx.variableOrder, point, boundCandidate));
    assert(isPointRootOfPoly(ctx.variableOrder, point, boundCandidate));

    // Do a "model-based" Brown-McCallum projection.
    std::vector<TaggedPoly> projectionResult;
    const auto& mainVariable = ctx.variableOrder[boundCandidate.level];
    if (std::holds_alternative<Section>(cell[boundCandidate.level])) {
      projectionResult.emplace_back({
          PolyTag::ORDER_INVARIANT,
          resultant(
            mainVariable,
            boundCandidate.poly,
            std::get<Section>(cell[boundCandidate.level])->poly),
          0}); // hack: we compute the level later in this function

      if (boundCandidate.tag == PolyTag::ORDER_INVARIANT) {
        projectionResult.emplace_back({
          PolyTag::SIGN_INVARIANT,
          boundCandidate.poly.lcoeff(mainVariable),
          0}); // hack: we compute the level later in this function
        projectionResult.emplace_back({
          PolyTag::ORDER_INVARIANT,
          discriminant(boundCandidate.poly),
          0}); // hack: we compute the level later in this function
      }
    } else { // cellComponent is a Sector at 'boundCandidate's level
      projectionResult.emplace_back({
          PolyTag::SIGN_INVARIANT,
          boundCandidate.poly.lcoeff(mainVariable),
          0}); // hack: we compute the level later in this function
      projectionResult.emplace_back({
          PolyTag::ORDER_INVARIANT,
          discriminant(boundCandidate.poly),
          0}); // hack: we compute the level later in this function

      Sector& sectorAtLvl = std::get<Sector>(cell[boundCandidate.level]);

      if (sectorAtLvl.lowBound) {
        projectionResult.emplace_back({
          PolyTag::ORDER_INVARIANT,
          resultant(
            mainVariable,
            boundCandidate.poly,
            sectorAtLvl.lowBound->poly),
          0}); // hack: we compute the level later in this function
      }
      if (sectorAtLvl.highBound) {
        projectionResult.emplace_back({
          PolyTag::ORDER_INVARIANT,
          resultant(
            mainVariable,
            boundCandidate.poly,
            sectorAtLvl.highBound->poly),
          0}); // hack: we compute the level later in this function
      }
    }


    for (const auto& resultPoly : projectionResult) {
      if (resultPoly.isConstant())
        continue;
      // Hack: add the correct level here
      resultPoly = *polyLevel(ctx.variableOrder, resultPoly);

      if (shrinkCellWithIrreducibleFactorsOfPoly(ctx, polyLog, resultPoly, cell)
            == ShrinkResult::FAIL)
        return ShrinkResult::FAIL;
    }

    if (boundCandidate.tag == PolyTag::ORDER_INVARIANT ||
          std::holds_alternative<Sector>(cell[boundCandidate.level]))
    {
      if (refineNonNull(ctx, dynctx, boundCandidate, cell) == ShrinkResult::FAIL)
        return ShrinkResult::FAIL;

      shrinkSingleComponent(ctx, boundCandidate, cell);
    }

    polyLog.projectionPolys.emplace_back({
        PolyTag::SIGN_INVARIANT,
        boundCandidate.poly,
        boundCandidate.level});

    return ShrinkResult::SUCCESS;
  }

  /** Check if there is a root of the given polynomial---that becomes univariate
   * after pluggin in all but the last variable wrt. the given variableOrder---,
   * that lies between the given 'low' and 'high' bounds.
   */
  bool hasPolyLastVariableRootWithinBounds(
    const ShrinkContext& ctx,
    const RAN& low,
    const RAN& high,
    const MultiPoly& poly,
    const std::size_t polyLevel)
  {
    for (const RAN& candidate :
          allLastVariableRoots(ctx.variableOrder, poly, polyLevel, ctx.point))
    {
      if (low <= candidate && candidate <= high)
        return true;
    }
    return false;
  }

  shrinkCellWithNonRootPoint(
    const ShrinkContext& ctx,
    PolyLog& polyLog,
    const TaggedPoly& boundCandidate,
    Cell& cell)
  {
    // This function is called "MergeNotRoot" in [1]
    // precondition:
    assert(isNonConstantIrreducible(boundCandidate.poly));
    assert(!isPointRootOfPoly(ctx.variableOrder, point, boundCandidate));

    // Do a "model-based" Brown-McCallum projection.
    std::vector<TaggedPoly> projectionResult;
    const auto& mainVariable = ctx.variableOrder[boundCandidate.level];
    if (std::holds_alternative<Section>(cell[boundCandidate.level])) {
      Section& sectionAtLvl = std::get<Section>(cell[boundCandidate.level]);
      projection.emplace_back({
        PolyTag::ORDER_INVARIANT,
        resultant(mainVariable, boundCandidate.poly, sectionAtLvl.poly),
        0}); // hack: we compute the level later in this function});
    } else { // cellComponent is a Sector at 'boundCandidate's level
      projectionResult.emplace_back({
        PolyTag::ORDER_INVARIANT,
        discriminant(mainVariable, boundCandidate.poly),
        0}); // hack: we compute the level later in this function});

      if (!sectorAtLvl.lowBound || !sectorAtLvl.highBound ||
            hasPolyLastVariableRootWithinBounds(
              ctx,
              sectorAtLvl.lowBound->cachedPoint,
              sectorAtLvl.highBound->cachedPoint,
              boundCandidate.poly,
              boundCandidate.level))
      {
        projectionResult.emplace_back({
          PolyTag::SIGN_INVARIANT,
          boundCandidate.poly.lcoeff(mainVariable),
          0}); // hack: we compute the level later in this function});
      }

      if (sectorAtLvl.lowBound)) {
        projectionResult.emplace_back({
          PolyTag::ORDER_INVARIANT,
          resultant(
            mainVariable,
            boundCandidate.poly,
            sectorAtLvl.lowBound->poly),
          0}); // hack: we compute the level later in this function});
      }
      if (sectorAtLvl.highBound)) {
        projectionResult.emplace_back({
          PolyTag::ORDER_INVARIANT,
          resultant(
            mainVariable,
            boundCandidate.poly,
            sectorAtLvl.highBound->poly)
          0}); // hack: we compute the level later in this function});
      }

    }

    for (const auto& resultPoly : projectionResult) {
      if (resultPoly.isConstant())
        continue;

      // Hack: add the correct level here
      resultPoly = *polyLevel(ctx.variableOrder, resultPoly);
      if (shrinkCellWithIrreducibleFactorsOfPoly(ctx, polyLog, resultPoly, cell)
            == ShrinkResult::FAIL)
        return ShrinkResult::FAIL;
    }

    if (std::holds_alternative<Sector>(cell[boundCandidate.level])) {
      if (refineNonNull(ctx, dynctx, boundCandidate, boundCandidate.level, cell)
            == ShrinkResult::FAIL)
        return ShrinkResult::FAIL;

      shrinkSingleComponent(ctx, boundCandidate, cell);
    }

    polyLog.projectionPolys.emplace_back({
      PolyTag::SIGN_INVARIANT,
      boundCandidate.poly,
      boundCandidate.level});

    return ShrinkResult::SUCCESS;
  }


  /**
   * Merge the given open OpenCADCell 'cell' that contains the given 'point'
   * (called "alpha" in [1]) with a polynomial 'poly'.
   * Before the merge 'cell' represents a region that is sign-invariant
   * on other (previously merged) polynomials (all signs are non-zero).
   * The returned cell represents a region that is additionally sign-invariant on
   * 'poly' (also with non-zero sign).
   * @return either an OpenCADCell or nothing (representing a failed construction)
   */
  ShrinkResult shrinkCell(
    const ShrinkContext& ctx,
    PolyLog& polyLog,
    const TaggedPoly& boundCandidate,
    CADCell& cell)
  {
    // This function is called "Merge" in [1]
    // precondition:
    assert(isPointInsideCell(ctx.variableOrder, ctx.point, cell));

    if (isAlreadyProcessed(polyLog, boundCandidate))
      return ShrinkResult::SUCCESS;

    if (cellDimension(cell, boundCandidate.level) == 0) {
      polyLog.projectionPolys.emplace_back({ORDER_INVARIANT, boundCandidate.poly});
      return ShrinkResult::SUCCESS;
    }

    if (boundCandidate.level == 0) {
      if (std::holds_alternative<Sector>(cell[boundCandidate.level]))
        shrinkSingleComponent(ctx, boundCandidate, cell);
      polyLog.projectionPolys.emplace_back({ORDER_INVARIANT, boundCandidate.poly});
      return ShrinkResult::SUCCESS;
    }

    if (vanishesEarly(ctx.variableOrder, ctx.point, boundCandidate))
      return shrinkCellWithEarlyVanishingPoly(ctx, polyLog, boundCandidate, cell);

    // lower level subcell
    if (cellDimension(cell, boundCandidate.level-1) == 0) {
      shrinkSingleComponent(ctx, boundCandidate, cell);
      polyLog.projectionPolys.emplace_back({ORDER_INVARIANT, boundCandidate.poly});
      return ShrinkResult::SUCCESS;
    }

    if (isPointRootOfPoly(ctx.variableOrder, point, boundCandidate))
      return shrinkCellWithPolyHavingPointAsRoot(ctx, polyLog, boundCandidate, cell);
    else
      return shrinkCellWithNonRootPoint(ctx, polyLog, boundCandidate, cell);

    return newCell;
  }

  /**
   * Construct a single CADCell that contains the given 'point' and is
   * sign-invariant for the given polynomials in 'polys'.  The construction
   * fails if 'polys' are not well-oriented [2].  Note that
   * this cell is cylindrical only with respect to the given 'variableOrder'.
   *
   * @param variableOrder must contain unique variables and at least one,
   * because constant polynomials (without a variable) are prohibited.
   * @param point point.size() >= variables.size().
   * @param polys must contain only non-constant, irreducible polynomials that
   * mention only variables that appear in 'variableOrder'.
   *
   */
  std::option<CADCell> buildPointEnclosingCADCell(
    const std::vector<carl::Variable>& variableOrder,
    const RANPoint& point,
    const std::vector<MultiPoly>& polys)
  {
    // precondition:
    assert(!variableOrder.empty());
    assert(hasNoDuplicates(variableOrder));
    assert(variableOrder.size() <= point.dim());
    assert(containsOnlyNonConstantIrreduciblePolys(polys));
    assert(polyVariablesAreAllFromPredefinedSet(polys, variableOrder));

    SMTRAT_LOG_INFO("smtrat.onecellcad", "Create OneCellCADCell");
    SMTRAT_LOG_DEBUG("smtrat.onecellcad", "Use point " << point << " wrt. variable order " << variableOrder);

    CADCell cell = buildFullspaceCoveringCell(point.dim());

    carl::CoCoAAdaptor<MultiPoly> factorizer(polys);
    const ShrinkContext ctx{point, variableOrder, factorizer};
    PolyLog emptyLog;
    for(const auto& poly : polys){
      SMTRAT_LOG_INFO("smtrat.onecellcad", "Merge input poly");
      SMTRAT_LOG_DEBUG("smtrat.onecellcad", "Input poly: " << poly);
      const size_t polyLevel = *polyLevel(ctx.variableOrder, variableOrder);
      const TaggedPoly tagged = {PolyTag::SIGN_INVARIANT, poly, polyLevel};
      if (shrinkCell(ctx, emptyLog, taggedPoly, cell) == ShrinkResult::FAIL) {
        SMTRAT_LOG_WARN("smtrat.onecellcad", "Construction failed");
        return std::nullopt;
      }
    }
    SMTRAT_LOG_DEBUG("smtrat.onecellcad", "Final cell: " << cell);
    return cell;
  }

} // namespace onecellcad
} // namespace smtrat

//TODO add assertions
//TODO check all level indexes
//TODO check polylevels of subpolys
//TODO check variable copy by value, not reference
//TODO heck
