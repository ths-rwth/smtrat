#pragma once

/**
 * @file
 * Construct a single open CAD Cell around a given point that is sign-invariant
 * on a given set of polynomials.
 *
 * References:
 * [brown15] Brown, Christopher W., and Marek Košta.
 * "Constructing a single cell in cylindrical algebraic decomposition."
 * Journal of Symbolic Computation 70 (2015): 14-48.
 * [mccallum84] Scott McCallum.
 * "An Improved Projection Operation for Cylindrical Algebraic Decomposition"
 * Ph.D. Dissertation. 1984. The University of Wisconsin - Madison
 */

#include <vector>
#include <unordered_map>
#include <set>
#include <algorithm>
#include "variant.hpp" // Workaround; remove when c++17 available
#include <experimental/optional> // remove when c++17 available
/* #include <optional> // uncomment when c++17 is available*/

#include <carl/formula/model/ran/RealAlgebraicNumber.h>
#include <carl/formula/model/ran/RealAlgebraicNumberEvaluation.h>
#include <carl/formula/model/ran/RealAlgebraicPoint.h>
#include <carl/core/Variable.h>
#include <carl/core/VariablePool.h>
#include <carl/core/polynomialfunctions/Resultant.h>
#include <carl/core/rootfinder/RootFinder.h>
#include <carl/core/UnivariatePolynomial.h>
#include <carl/core/MultivariatePolynomial.h>
#include <carl/converter/CoCoAAdaptor.h>

#include "../../../Common.h" // useful short type aliases and constants
#include "Assertables.h"

namespace smtrat {
namespace onecellcad {

    using UniPoly = carl::UnivariatePolynomial<smtrat::Rational>;
    using MultiCoeffUniPoly = carl::UnivariatePolynomial<Poly>;
    using RAN = carl::RealAlgebraicNumber<smtrat::Rational>;
    using RANPoint = carl::RealAlgebraicPoint<smtrat::Rational>;
    using RANMap = std::map<carl::Variable, RAN>;

    enum class PolyTag {
      ORD_INV, SGN_INV
    };

    inline
    std::ostream &operator<<(std::ostream &o, const PolyTag &p) {
      switch (p) {
        case PolyTag::ORD_INV  :
          return o << "ORD_INV";
        case PolyTag::SGN_INV :
          return o << "SGN_INV";
      }
      return o;
    }

    enum class ShrinkResult {
      SUCCESS, FAIL
    };

    inline
    std::ostream &operator<<(std::ostream &o, const ShrinkResult &s) {
      switch (s) {
        case ShrinkResult::SUCCESS  :
          return o << "SUCCESS";
        case ShrinkResult::FAIL :
          return o << "FAIL";
      }
      return o;
    }

    struct TagPoly2 {
      PolyTag tag;

      Poly poly;

      /** Workaround: Cache the poly's level to avoid recomputing it in many places. */
      std::size_t level;
    };

    inline
    std::ostream &operator<<(std::ostream &o, const TagPoly2 &p) {
      return o << "(poly " << p.tag << " " << p.poly << ")";
    }

    inline
    bool operator==(const TagPoly2 &lhs, const TagPoly2 &rhs) {
      return lhs.tag == rhs.tag && lhs.poly == rhs.poly;
    }

    struct TagPoly {
      PolyTag tag;
      Poly poly;
    };

    inline
    bool operator==(const TagPoly &lhs, const TagPoly &rhs) {
      return lhs.tag == rhs.tag && lhs.poly == rhs.poly;
    }

    inline
    std::ostream &operator<<(std::ostream &o, const TagPoly &p) {
      return o << "(poly " << p.tag << " " << p.poly << ")";
    }

    inline
    std::ostream &operator<<(std::ostream &o, const std::vector<TagPoly> &polys) {
      o << "[ " << polys.size() << ": ";
      for (const auto& poly : polys)
        o << poly.tag << " " << poly.poly << ", ";
      return o << "]";
    }

    inline
    std::ostream &operator<<(std::ostream &o, const std::vector<TagPoly2> &polys) {
      o << "[ " << polys.size() << ": ";
      for (const auto& poly : polys)
        o << poly.tag << " " << poly.poly << ", ";
      return o << "]";
    }

    inline
    std::vector<Poly> asMultiPolys(const std::vector<TagPoly2> polys){
      std::vector<Poly> mPolys;
      for (const auto& poly : polys)
        mPolys.emplace_back(poly.poly);
      return mPolys;
    }

    inline
    std::vector<Poly> asMultiPolys(const std::vector<TagPoly> polys){
      std::vector<Poly> mPolys;
      for (const auto& poly : polys)
        mPolys.emplace_back(poly.poly);
      return mPolys;
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
      Poly poly;

      RAN lastVarCachedRoot;

      /** Workaround: Store root number of poly. TODO convert to MultivariateRoot someday */
      std::size_t rootNumber;
    };

    inline
    std::ostream &operator<<(std::ostream &o, const Section &s) {
      return o << "(section " << s.poly << " " << s.lastVarCachedRoot << ")";
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
      std::experimental::optional<Section> lowBound;

      /** A std:nullopt highBound represents infinity */
      std::experimental::optional<Section> highBound;
    };

    inline
    std::ostream &operator<<(ostream &o, const Sector &s) {
      o << "(sector ";
      s.lowBound ? o << s.lowBound.value() : o << "-infty";
      o << " ";
      s.highBound ? o << s.highBound.value() : o << "infty";
      return o << ")";
    }

    /**
     * Represent a single cell [1].
     * A cell is a collection of boundary objects along each axis, called
     * cell-components based on math. vectors and their components.
     */
    using CADCell = std::vector<mpark::variant<Sector, Section>>;

    inline
    std::ostream &operator<<(ostream &o, const CADCell &c) {
      o << "(cell";
      for (int i = 0; i < c.size(); i++) {
        o << " " << i << " ";
        if (mpark::holds_alternative<Sector>(c[i])) {
          o << mpark::get<Sector>(c[i]);
        } else {
          o << mpark::get<Section>(c[i]);
        }
      }
      return o << ")";
    }

    /**
     * @return Dimension of a hybercube to which the given cell is homeomorphic,
     * i.e., count the number of sectors of the given Cell restricted to its first
     * components (with index 0 to 'uptoLevel').
     */
    inline
    std::size_t cellDimension(const CADCell &cell, const std::size_t uptoLevel) {
      std::size_t sectorCount = 0;
      for (std::size_t i = 0; i <= uptoLevel; i++)
        if (mpark::holds_alternative<Sector>(cell[i]))
          sectorCount++;
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
      const carl::CoCoAAdaptor<Poly> factorizer;
    };


    /**
     * Store all processed polys.
     */
    struct PolyLog {
      /** This collection is called "P_prj" in [1] */
      std::vector<TagPoly2> projectionPolys;

      /** Only delinating polys. This collection is called "P_dln" in [1] */
      std::vector<TagPoly2> delineators;
    };


    /**
     * Find the index of the highest variable (wrt. the ordering
     * in 'variableOrder') that occurs with positive degree in 'poly'.
     * Although 'level' is a math concept that starts counting at 1
     * we start counting at 0 and represent "no level/variable" as std::nullopt
     * because it simplifies using the level directly as an index into arrays
     * or vectors.
     * Examples:
     * - polyLevel(2) == nullopt wrt. any variable order
     * - polyLevel(0*x+2) == nullopt wrt. any variable order
     * - polyLevel(x+2) == 0 wrt. [x < y < z]
     * - polyLevel(x+2) == 1 wrt. [y < x < z]
     * - polyLevel(x+2) == 2 wrt. [y < z < x]
     * - polyLevel(x*y+2) == 1 wrt. [x < y < z] because of y
     * - polyLevel(x*y+2) == 1 wrt. [y < x < z] because of x
     * - polyLevel(x*y+2) == 2 wrt. [x < z < y] because of y
     * Preconditions:
     * - 'poly.gatherVariables()' must be a subset of 'variableOrder'.
     */
    inline
    std::experimental::optional<std::size_t> levelOf(
      const std::vector<carl::Variable> &variableOrder,
      const Poly &poly) {
      // precondition:
      assert(isSubset(asVector(poly.gatherVariables()), variableOrder));

      // Algorithm:
      // Iterate through each variable inside 'variableOrder' in ascending order
      // and remove it from 'polyVariables'. The last variable in 'polyVariables' before
      // it becomes empty is the highest appearing variable in 'poly'.

      // 'gatherVariables()' collects only variables with positive degree
      auto polyVariables = poly.gatherVariables();

      if (polyVariables.empty())
        return std::experimental::nullopt; // for const-polys like '2'

      for (int level = 0; level < variableOrder.size(); ++level) {
        polyVariables.erase(variableOrder[level]);
        // Last variable before 'polyVariables' becomes empty is the highest variable.
        if (polyVariables.empty())
          return level;
      }
      throw ("Poly contains variable not found in variableOrder");
    }

  class OneCellCAD {
    public:

    inline
    CADCell fullSpaceCoveringCell(std::size_t cellComponentCount) {
      return CADCell(cellComponentCount);
    }

    /**
     * Create a mapping from the first variables (with index 0 to 'level') in the
     * given 'variableOrder' to the first components of the given 'point'.
     */
    std::map<carl::Variable, RAN> toStdMap(
      const std::vector<carl::Variable> &variableOrder,
      const std::size_t componentCount,
      const RANPoint &point) {
      std::map<carl::Variable, RAN> varToRANMap;
      for (std::size_t i = 0; i < componentCount; i++)
        varToRANMap[variableOrder[i]] = point[i];
      return varToRANMap;
    }

    /**
     * Given a poly p(x1,..,xn), return all roots of the univariate poly
     * p(a1,..,an-1, xn), where a1,..an-1 are the first algebraic real components
     * from 'point'.
     */
    std::vector<RAN> allLastVariableRoots(
      const std::vector<carl::Variable> &variableOrder,
      const RANPoint &point,
      const std::size_t polyLevel,
      const Poly &poly) {
      // 'realRoots' returns std::nullopt if poly vanishes
      // early, but here we don't care
      auto rootsOpt = carl::rootfinder::realRoots(
        poly.toUnivariatePolynomial(variableOrder[polyLevel]),
        toStdMap(variableOrder, polyLevel, point));
      if (rootsOpt)
        return *rootsOpt;
      else
        return {};
    }

    inline
    bool contains(const std::vector<TagPoly2> &polys, const Poly &poly) {
      auto isMatch = [&poly](const TagPoly2 &taggedPoly) {
        return taggedPoly.poly == poly;
      };
      return std::find_if(polys.begin(), polys.end(), isMatch) != polys.end();
    }

    template<typename T>
    bool contains(const std::vector<T> &polys, const T &poly) {
      return std::find(polys.begin(), polys.end(), poly) != polys.end();
    }

    bool isAlreadyProcessed(const PolyLog &log, const TagPoly2 &poly) {
      // matches if poly is found with its tag or an oi-tag
      auto isMatch = [&poly](const TagPoly2 &processedPoly) {
        return processedPoly.poly == poly.poly &&
               (processedPoly.tag == poly.tag
                || processedPoly.tag == PolyTag::ORD_INV);
      };
      if (std::find_if(log.projectionPolys.begin(), log.projectionPolys.end(), isMatch)
          != log.projectionPolys.end())
        return true;

      return std::find_if(log.delineators.begin(), log.delineators.end(), isMatch)
             != log.delineators.end();
    }

    /**
     * Check if an n-variate 'poly' p(x1,..,xn) with n>=1 already becomes the
     * zero poly after plugging in p(a1,..,an-1, xn), where a1,..an-1 are the
     * first n-1 algebraic real components from 'point'.
     */
    inline
    bool vanishesEarly(
      const std::vector<carl::Variable> &variableOrder,
      const RANPoint &point,
      const std::size_t polyLevel,
      const Poly &poly) {
      // precondition:
      assert(!poly.isConstant());
      if (poly.isLinear())
        return false;

      const carl::Variable mainVariable = variableOrder[polyLevel];
      std::map<carl::Variable, carl::Interval<Rational>> dummy;
      auto resultPoly =
        carl::RealAlgebraicNumberEvaluation::evaluateCoefficients(
          poly.toUnivariatePolynomial(mainVariable),
          toStdMap(variableOrder, polyLevel, point),
          dummy);
      return resultPoly.isZero();
    }

    bool isPointRootOfPoly(
      const std::vector<carl::Variable> &variableOrder,
      const RANPoint &point,
      const std::size_t polyLevel,
      const Poly &poly) {
      const std::size_t componentCount = polyLevel + 1;
      std::vector<carl::Variable> subVariableOrder(
        variableOrder.begin(),
        variableOrder.begin() + componentCount);
      // 'evaluate' only accepts a point and variables with exactly
      // 'componentCount' number of components
      RAN result = carl::RealAlgebraicNumberEvaluation::evaluate(
        poly,
        point.subpoint(componentCount),
        subVariableOrder
      );
      return result.isZero();
    }

    inline
    bool isPointRootOfPoly(
      const std::vector<carl::Variable> &variableOrder,
      const RANPoint &point,
      const TagPoly2 &poly) {
      return isPointRootOfPoly(variableOrder, point, poly.level, poly.poly);
    }

    bool isPointInsideCell(
      const std::vector<carl::Variable> &variableOrder,
      const RANPoint &point,
      const CADCell &cell) {
      // precondition
      assert(point.dim() >= 1);
      assert(cell.size() <= point.dim());

      for (std::size_t level = 0; level < point.dim(); level++) {
        if (mpark::holds_alternative<Section>(cell[level])) {
          const Section section = mpark::get<Section>(cell[level]);
          if (!isPointRootOfPoly(variableOrder, point, level, section.poly))
            return false;
          if (section.lastVarCachedRoot != point[level])
            return false;
        } else {
          const Sector sector = mpark::get<Sector>(cell[level]);
          if (sector.highBound) {
            const Section highBound = *sector.highBound;
            if (point[level] > highBound.lastVarCachedRoot)
              return false;
            if (!isSubset(
              std::vector<RAN>{highBound.lastVarCachedRoot},
              allLastVariableRoots(variableOrder, point, level, highBound.poly))) {
              return false;
            }
          }
          if (sector.lowBound) {
            const Section lowBound = *sector.lowBound;
            if (point[level] < lowBound.lastVarCachedRoot)
              return false;
            if (!isSubset(
              std::vector<RAN>{lowBound.lastVarCachedRoot},
              allLastVariableRoots(variableOrder, point, level, lowBound.poly))) {
              return false;
            }
          }
        }
      }
      return true;
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
      const ShrinkContext &ctx,
      const std::size_t polyLevel,
      const Poly &poly,
      CADCell &cell) {
      // This function is called "Update" in [1]
      // precondition:
      assert(isNonConstIrreducible(poly));
      assert(!vanishesEarly(ctx.variableOrder, ctx.point, polyLevel, poly));
      if (mpark::holds_alternative<Section>(cell[polyLevel]))
        return; // canot shrink further

      Sector &sectorAtLvl = mpark::get<Sector>(cell[polyLevel]);
      RAN value = ctx.point[polyLevel]; // called alpha_k in [1]
      SMTRAT_LOG_DEBUG("smtrat.cad", "Shrink single cell sector");
      SMTRAT_LOG_TRACE("smtrat.cad", "Cell: " << cell);
      SMTRAT_LOG_TRACE("smtrat.cad", "Sector: " << polyLevel
                                                << " " << sectorAtLvl);
      SMTRAT_LOG_DEBUG("smtrat.cad", "Poly: " << poly);
      SMTRAT_LOG_TRACE("smtrat.cad", "Last variable: " << ctx.variableOrder[polyLevel]);
      SMTRAT_LOG_TRACE("smtrat.cad", "Point: " << ctx.point.subpoint(polyLevel + 1));
      // Isolate real roots of level-k 'poly' after plugin in a level-(k-1) point.
      // Poly must not vanish under this subpoint!
      auto roots =
        allLastVariableRoots(ctx.variableOrder, ctx.point, polyLevel, poly);
      if (roots.empty()) {
        SMTRAT_LOG_TRACE("smtrat.cad", "No last variable roots");
        return;
      }
      SMTRAT_LOG_TRACE("smtrat.cad", "Last variable roots: " << roots);

      // Search for closest roots/boundPoints to value, i.e.
      // someRoot ... < closestLower <= value <= closestUpper < ... someOtherRoot
      std::experimental::optional<RAN> closestLower;
      std::experimental::optional<RAN> closestUpper;

      std::size_t rootNumber = 0, lowerRootNumber, upperRootNumber;
      for (const auto &boundPointCandidate: roots) {
        rootNumber++;
        if (boundPointCandidate < value) {
          if (!closestLower || *closestLower < boundPointCandidate) {
            closestLower = boundPointCandidate;
            lowerRootNumber = rootNumber;
          }
        } else if (boundPointCandidate == value) {
          // Sector collapses into a section
          cell[polyLevel] = Section{poly, boundPointCandidate, rootNumber};
          SMTRAT_LOG_TRACE("smtrat.cad", "Sector collapses: " << (Section{poly, boundPointCandidate, rootNumber}));
          return;
        } else { // value < boundPointCandidate
          if (!closestUpper || boundPointCandidate < *closestUpper) {
            closestUpper = boundPointCandidate;
            upperRootNumber = rootNumber;
          }
        }
      }

      // Sector is still a sector
      if (closestLower)
        sectorAtLvl.lowBound = Section{poly, *closestLower, lowerRootNumber};

      if (closestUpper)
        sectorAtLvl.highBound = Section{poly, *closestUpper, upperRootNumber};

      SMTRAT_LOG_TRACE("smtrat.cad", "New component: " << polyLevel
                                                       << " " << sectorAtLvl);
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
    std::vector<Poly> partialDerivativesLayerWithSomeNonEarlyVanishingPoly(
      const std::vector<carl::Variable> &variableOrder,
      const RANPoint &point,
      const TagPoly2 &mainPoly) {
      assert(!mainPoly.poly.isConstant());
      // We search for this set of partial derivatives "layer by layer".
      // The layer of 0-th partial derivatives is the mainPoly itself.
      std::vector<Poly> layerOfDerivatives;
      layerOfDerivatives.emplace_back(mainPoly.poly);
      bool foundSomeNonEarlyVanishingDerivative = false;

      do {
        std::vector<Poly> nextLayer;
        for (const auto &poly : layerOfDerivatives) {
          // Derive poly wrt to each variable (variables with idx 0 to 'mainPoly.level')
          for (std::size_t varIdx = 0; varIdx <= mainPoly.level; varIdx++) {
            const auto derivative = poly.derivative(variableOrder[varIdx]);
            if (derivative.isZero())
              continue;
            nextLayer.emplace_back(derivative);
            if (foundSomeNonEarlyVanishingDerivative)
              continue; // avoid expensive vanishing check

            if (derivative.isConstant() ||
                !vanishesEarly(variableOrder, point, mainPoly.level, mainPoly.poly))
              foundSomeNonEarlyVanishingDerivative = true;
            // still need to compute all remaining nextLayer-polys
          }
        }
        layerOfDerivatives = std::move(nextLayer);
      } while (!foundSomeNonEarlyVanishingDerivative);

      return layerOfDerivatives;
    }

    inline
    Poly discriminant(const carl::Variable &mainVariable, const Poly &p) {
      return Poly(carl::discriminant(p.toUnivariatePolynomial(mainVariable)));
    }


    ShrinkResult refineNull(
      const ShrinkContext &ctx,
      PolyLog &polyLog,
      const TagPoly2 &boundCandidate,
      CADCell &cell) {
      // This function is called "RefNull" in [1]
      // precondition:
      assert(isNonConstIrreducible(boundCandidate.poly));
      assert(isPointRootOfPoly(ctx.variableOrder, ctx.point, boundCandidate));
      SMTRAT_LOG_TRACE("smtrat.cad", "RefineNull");
      const auto mainVariable = ctx.variableOrder[boundCandidate.level];
      const auto boundCandidateUniPoly =
        boundCandidate.poly.toUnivariatePolynomial(mainVariable);
      std::vector<TagPoly2> projectionResult;

      projectionResult.emplace_back(TagPoly2{
        PolyTag::ORD_INV,
        discriminant(mainVariable, boundCandidate.poly),
        0}); // hack: we compute the level later in this function

      projectionResult.emplace_back(TagPoly2{
        PolyTag::ORD_INV,
        boundCandidateUniPoly.lcoeff(),
        0}); // hack: we compute the level later in this function

      projectionResult.emplace_back(TagPoly2{
        PolyTag::ORD_INV,
        boundCandidateUniPoly.tcoeff(),
        0}); // hack: we compute the level later in this function

      for (auto &resultPoly : projectionResult) {
        if (resultPoly.poly.isConstant())
          continue;

        // Hack: add the correct level here
        resultPoly.level = *levelOf(ctx.variableOrder, resultPoly.poly);
        if (shrinkCellWithIrreducibleFactorsOfPoly(ctx, polyLog, resultPoly, cell)
            == ShrinkResult::FAIL)
          return ShrinkResult::FAIL;
      }

      return ShrinkResult::SUCCESS;
    }


    ShrinkResult shrinkCellWithEarlyVanishingPoly(
      const ShrinkContext &ctx,
      PolyLog &polyLog,
      const TagPoly2 &boundCandidate,
      CADCell &cell) {
      // This function is called MergeNull in [1]
      // precondition:
      assert(vanishesEarly(ctx.variableOrder, ctx.point, boundCandidate.level, boundCandidate.poly));
      assert(isNonConstIrreducible(boundCandidate.poly));
      SMTRAT_LOG_TRACE("smtrat.cad", "ShrinkWithEarlyVanishingPoly");

      auto shrinkResult = refineNull(ctx, polyLog, boundCandidate, cell);
      if (shrinkResult == ShrinkResult::FAIL)
        return shrinkResult;

      if (boundCandidate.tag == PolyTag::SGN_INV) {
        polyLog.projectionPolys.emplace_back(boundCandidate);
        return ShrinkResult::SUCCESS;
      } else { //boundCandidate.tag == PolyTag::ORD_INV
        if (cellDimension(cell, boundCandidate.level - 1) > 0)
          return ShrinkResult::FAIL;

        // Construct a delineating poly as the sum of all non-earlyVanishing,
        // squared m-th partial derivatives.
        Poly delineator(0);
        for (const auto &poly :
          partialDerivativesLayerWithSomeNonEarlyVanishingPoly(
            ctx.variableOrder, ctx.point, boundCandidate)) {
          if (!vanishesEarly(ctx.variableOrder, ctx.point, boundCandidate.level, boundCandidate.poly))
            delineator += poly * poly;
        }

        if (!delineator.isConstant()) {
          const size_t delineatorLevel = *levelOf(ctx.variableOrder, delineator);
          shrinkSingleComponent(ctx, delineatorLevel, delineator, cell);

          const TagPoly2 taggedDelineator{
            PolyTag::ORD_INV,
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
    Poly resultant(const carl::Variable &mainVariable, const Poly &p1, const Poly &p2) {
      const auto p1UPoly = p1.toUnivariatePolynomial(mainVariable);
      const auto p2UPoly = p2.toUnivariatePolynomial(mainVariable);
      return Poly(carl::resultant(p1UPoly, p2UPoly));
    }

    ShrinkResult shrinkCellWithIrreducibleFactorsOfPoly(
      const ShrinkContext &ctx,
      PolyLog &polyLog,
      const TagPoly2 &poly,
      CADCell &cell) {
      for (const auto &factor : ctx.factorizer.irreducibleFactorsOf(poly.poly)) {
        SMTRAT_LOG_TRACE("smtrat.cad", "Shrink with irreducible factor: Poly: "
          << poly.poly << " Factor: " << factor);
        if (factor.isConstant())
          continue;

        const std::size_t factorLevel = *levelOf(ctx.variableOrder, factor);
        TagPoly2 factorWithInheritedTag{poly.tag, factor, factorLevel};
        if (shrinkCell(ctx, polyLog, factorWithInheritedTag, cell)
            == ShrinkResult::FAIL)
          return ShrinkResult::FAIL;
      }
      return ShrinkResult::SUCCESS;
    }

    ShrinkResult refineNonNull(
      const ShrinkContext &ctx,
      PolyLog &polyLog,
      const TagPoly2 &boundCandidate,
      CADCell &cell) {
      // This function is called "RefNonNull" in [1]
      // precondition:
      assert(isNonConstIrreducible(boundCandidate.poly));
      assert(!vanishesEarly(ctx.variableOrder, ctx.point, boundCandidate.level, boundCandidate.poly));
      SMTRAT_LOG_TRACE("smtrat.cad", "RefineNonNull");

      const auto mainVariable = ctx.variableOrder[boundCandidate.level];
      const auto boundCandidateUniPoly =
        boundCandidate.poly.toUnivariatePolynomial(mainVariable);

      // Do early-exit tests:
      for (const auto &coeff : boundCandidateUniPoly.coefficients()) {
        if (coeff.isConstant() && !coeff.isZero())
          return ShrinkResult::SUCCESS;
      }

      const auto &leadCoeff = boundCandidate.poly.lcoeff(mainVariable);
      if ((contains(polyLog.projectionPolys, leadCoeff)
           || contains(polyLog.delineators, leadCoeff))
          && !isPointRootOfPoly(ctx.variableOrder, ctx.point, *levelOf(ctx.variableOrder, leadCoeff), leadCoeff)) {
        return ShrinkResult::SUCCESS;
      }

      const auto discrim = discriminant(mainVariable, boundCandidate.poly);
      if ((contains(polyLog.projectionPolys, discrim)
           || contains(polyLog.delineators, discrim))
          && !isPointRootOfPoly(ctx.variableOrder, ctx.point, *levelOf(ctx.variableOrder, discrim), discrim)) {
        return ShrinkResult::SUCCESS;
      }

      // optional early-exit check: if for every point in subcell, poly does not
      // vanish, return success. No idea how to do that efficiently.

      for (const auto &coeff : boundCandidateUniPoly.coefficients()) {
        // find first non-vanishing coefficient:
        const auto coeffLevel = *levelOf(ctx.variableOrder, coeff); // certainly non-constant
        if (!isPointRootOfPoly(ctx.variableOrder, ctx.point, coeffLevel, coeff)) {
          return
            shrinkCellWithIrreducibleFactorsOfPoly(
              ctx,
              polyLog,
              {PolyTag::SGN_INV, coeff, coeffLevel},
              cell);
        }
      }
      return ShrinkResult::SUCCESS;
    }


    ShrinkResult shrinkCellWithPolyHavingPointAsRoot(
      const ShrinkContext &ctx,
      PolyLog &polyLog,
      const TagPoly2 &boundCandidate,
      CADCell &cell) {
      // This function is called MergeRoot in [1]
      // precondition:
      assert(!vanishesEarly(ctx.variableOrder, ctx.point, boundCandidate.level, boundCandidate.poly));
      assert(isPointRootOfPoly(ctx.variableOrder, ctx.point, boundCandidate));
      SMTRAT_LOG_TRACE("smtrat.cad", "ShrinkWithPolyHavingPointAsRoot");

      // Do a "model-based" Brown-McCallum projection.
      std::vector<TagPoly2> projectionResult;
      const auto mainVariable = ctx.variableOrder[boundCandidate.level];
      if (mpark::holds_alternative<Section>(cell[boundCandidate.level])) {
        projectionResult.emplace_back(TagPoly2{
          PolyTag::ORD_INV,
          resultant(
            mainVariable,
            boundCandidate.poly,
            mpark::get<Section>(cell[boundCandidate.level]).poly),
          0}); // hack: we compute the level later in this function

        if (boundCandidate.tag == PolyTag::ORD_INV) {
          projectionResult.emplace_back(TagPoly2{
            PolyTag::SGN_INV,
            boundCandidate.poly.lcoeff(mainVariable),
            0}); // hack: we compute the level later in this function
          projectionResult.emplace_back(TagPoly2{
            PolyTag::ORD_INV,
            discriminant(mainVariable, boundCandidate.poly),
            0}); // hack: we compute the level later in this function
        }
      } else { // cellComponent is a Sector at 'boundCandidate's level
        projectionResult.emplace_back(TagPoly2{
          PolyTag::SGN_INV,
          boundCandidate.poly.lcoeff(mainVariable),
          0}); // hack: we compute the level later in this function
        projectionResult.emplace_back(TagPoly2{
          PolyTag::ORD_INV,
          discriminant(mainVariable, boundCandidate.poly),
          0}); // hack: we compute the level later in this function

        Sector &sectorAtLvl = mpark::get<Sector>(cell[boundCandidate.level]);

        if (sectorAtLvl.lowBound) {
          projectionResult.emplace_back(TagPoly2{
            PolyTag::ORD_INV,
            resultant(
              mainVariable,
              boundCandidate.poly,
              sectorAtLvl.lowBound->poly),
            0}); // hack: we compute the level later in this function
        }
        if (sectorAtLvl.highBound) {
          projectionResult.emplace_back(TagPoly2{
            PolyTag::ORD_INV,
            resultant(
              mainVariable,
              boundCandidate.poly,
              sectorAtLvl.highBound->poly),
            0}); // hack: we compute the level later in this function
        }
      }


      for (auto &resultPoly : projectionResult) {
        if (resultPoly.poly.isConstant())
          continue;
        // Hack: add the correct level here
        resultPoly.level = *levelOf(ctx.variableOrder, resultPoly.poly);

        if (shrinkCellWithIrreducibleFactorsOfPoly(ctx, polyLog, resultPoly, cell)
            == ShrinkResult::FAIL)
          return ShrinkResult::FAIL;
      }

      if (boundCandidate.tag == PolyTag::ORD_INV ||
          mpark::holds_alternative<Sector>(cell[boundCandidate.level])) {
        if (refineNonNull(ctx, polyLog, boundCandidate, cell) == ShrinkResult::FAIL)
          return ShrinkResult::FAIL;

        shrinkSingleComponent(ctx, boundCandidate.level, boundCandidate.poly, cell);
      }

      polyLog.projectionPolys.emplace_back(TagPoly2{
        PolyTag::SGN_INV,
        boundCandidate.poly,
        boundCandidate.level});

      return ShrinkResult::SUCCESS;
    }

    /** Check if there is a root of the given polynomial---that becomes univariate
     * after pluggin in all but the last variable wrt. the given variableOrder---,
     * that lies between the given 'low' and 'high' bounds.
     */
    bool hasPolyLastVariableRootWithinBounds(
      const ShrinkContext &ctx,
      const RAN &low,
      const RAN &high,
      const Poly &poly,
      const std::size_t polyLevel) {
      for (const RAN &candidate :
        allLastVariableRoots(ctx.variableOrder, ctx.point, polyLevel, poly)) {
        if (low <= candidate && candidate <= high)
          return true;
      }
      return false;
    }

    ShrinkResult shrinkCellWithNonRootPoint(
      const ShrinkContext &ctx,
      PolyLog &polyLog,
      const TagPoly2 &boundCandidate,
      CADCell &cell) {
      // This function is called "MergeNotRoot" in [1]
      // precondition:
      assert(isNonConstIrreducible(boundCandidate.poly));
      assert(!isPointRootOfPoly(ctx.variableOrder, ctx.point, boundCandidate));
      SMTRAT_LOG_TRACE("smtrat.cad", "ShrinkWithNonRootPoint");

      // Do a "model-based" Brown-McCallum projection.
      std::vector<TagPoly2> projectionResult;
      const auto mainVariable = ctx.variableOrder[boundCandidate.level];
      if (mpark::holds_alternative<Section>(cell[boundCandidate.level])) {
        Section sectionAtLvl = mpark::get<Section>(cell[boundCandidate.level]);
        projectionResult.emplace_back(TagPoly2{
          PolyTag::ORD_INV,
          resultant(mainVariable, boundCandidate.poly, sectionAtLvl.poly),
          0}); // hack: we compute the level later in this function});
      } else { // cellComponent is a Sector at 'boundCandidate's level
        projectionResult.emplace_back(TagPoly2{
          PolyTag::ORD_INV,
          discriminant(mainVariable, boundCandidate.poly),
          0}); // hack: we compute the level later in this function});

        Sector sectorAtLvl = mpark::get<Sector>(cell[boundCandidate.level]);
        if (!sectorAtLvl.lowBound || !sectorAtLvl.highBound ||
            hasPolyLastVariableRootWithinBounds(
              ctx,
              sectorAtLvl.lowBound->lastVarCachedRoot,
              sectorAtLvl.highBound->lastVarCachedRoot,
              boundCandidate.poly,
              boundCandidate.level)) {
          projectionResult.emplace_back(TagPoly2{
            PolyTag::SGN_INV,
            boundCandidate.poly.lcoeff(mainVariable),
            0}); // hack: we compute the level later in this function});
        }

        if (sectorAtLvl.lowBound) {
          projectionResult.emplace_back(TagPoly2{
            PolyTag::ORD_INV,
            resultant(
              mainVariable,
              boundCandidate.poly,
              sectorAtLvl.lowBound->poly),
            0}); // hack: we compute the level later in this function});
        }
        if (sectorAtLvl.highBound) {
          projectionResult.emplace_back(TagPoly2{
            PolyTag::ORD_INV,
            resultant(
              mainVariable,
              boundCandidate.poly,
              sectorAtLvl.highBound->poly),
            0}); // hack: we compute the level later in this function});
        }

      }

      for (auto resultPoly : projectionResult) {
        if (resultPoly.poly.isConstant())
          continue;

        // Hack: add the correct level here
        resultPoly.level = *levelOf(ctx.variableOrder, resultPoly.poly);
        if (shrinkCellWithIrreducibleFactorsOfPoly(ctx, polyLog, resultPoly, cell)
            == ShrinkResult::FAIL)
          return ShrinkResult::FAIL;
      }

      if (mpark::holds_alternative<Sector>(cell[boundCandidate.level])) {
        if (refineNonNull(ctx, polyLog, boundCandidate, cell)
            == ShrinkResult::FAIL)
          return ShrinkResult::FAIL;

        shrinkSingleComponent(ctx, boundCandidate.level, boundCandidate.poly, cell);
      }

      polyLog.projectionPolys.emplace_back(TagPoly2{
        PolyTag::SGN_INV,
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
      const ShrinkContext &ctx,
      PolyLog &polyLog,
      const TagPoly2 &boundCandidate,
      CADCell &cell) {
      // This function is called "Merge" in [1]
      // precondition:
      assert(isPointInsideCell(ctx.variableOrder, ctx.point, cell));

      SMTRAT_LOG_INFO("smtrat.cad", "Shrink cell");
      SMTRAT_LOG_DEBUG("smtrat.cad", "Poly: " << boundCandidate);
      SMTRAT_LOG_DEBUG("smtrat.cad", "Cell: " << cell);

      if (isAlreadyProcessed(polyLog, boundCandidate))
        return ShrinkResult::SUCCESS;

      if (cellDimension(cell, boundCandidate.level) == 0) {
        polyLog.projectionPolys.emplace_back(TagPoly2{PolyTag::ORD_INV, boundCandidate.poly, boundCandidate.level});
        return ShrinkResult::SUCCESS;
      }

      if (boundCandidate.level == 0) {
        if (mpark::holds_alternative<Sector>(cell[boundCandidate.level]))
          shrinkSingleComponent(ctx, boundCandidate.level, boundCandidate.poly, cell);
        polyLog.projectionPolys.emplace_back(TagPoly2{PolyTag::ORD_INV, boundCandidate.poly, boundCandidate.level});
        return ShrinkResult::SUCCESS;
      }

      if (vanishesEarly(ctx.variableOrder, ctx.point, boundCandidate.level, boundCandidate.poly))
        return shrinkCellWithEarlyVanishingPoly(ctx, polyLog, boundCandidate, cell);

      // lower level subcell
      if (cellDimension(cell, boundCandidate.level - 1) == 0) {
        shrinkSingleComponent(ctx, boundCandidate.level, boundCandidate.poly, cell);
        polyLog.projectionPolys.emplace_back(TagPoly2{PolyTag::ORD_INV, boundCandidate.poly, boundCandidate.level});
        return ShrinkResult::SUCCESS;
      }

      if (isPointRootOfPoly(ctx.variableOrder, ctx.point, boundCandidate))
        return shrinkCellWithPolyHavingPointAsRoot(ctx, polyLog, boundCandidate, cell);
      else
        return shrinkCellWithNonRootPoint(ctx, polyLog, boundCandidate, cell);
    }

    std::vector<TagPoly> oneLevelFullBrowMcCallumProjection(
      carl::CoCoAAdaptor<Poly> factorizer,
      carl::Variable mainVar,
      std::vector<TagPoly> polys) {

      std::vector<TagPoly> projectionResult;
      for (int i = 0; i < polys.size(); i++) {
        auto poly1 = polys[i];
        projectionResult.emplace_back(TagPoly{
          PolyTag::ORD_INV,
          discriminant(mainVar, poly1.poly)});
        projectionResult.emplace_back(TagPoly{
          PolyTag::SGN_INV,
          poly1.poly.lcoeff(mainVar)});
        for (int j = i + 1; j < polys.size(); j++) {
          auto poly2 = polys[j];
          auto resultantPoly =
            resultant(mainVar, poly1.poly, poly2.poly);
          projectionResult.emplace_back(TagPoly{
            PolyTag::ORD_INV,
            resultantPoly});
        }
      }
      std::vector<TagPoly> nextLevelNonConstIrreducibles;
      for (auto &poly : projectionResult) {
        if (poly.poly.isConstant())
          continue;

        for (const auto &factor : factorizer.irreducibleFactorsOf(poly.poly)) {
          TagPoly tFactor{poly.tag, factor};
          if (factor.isConstant() || contains(nextLevelNonConstIrreducibles, tFactor))
            continue;

          nextLevelNonConstIrreducibles.emplace_back(tFactor);
        }

      }
      return nextLevelNonConstIrreducibles;
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
    std::experimental::optional<CADCell> pointEnclosingCADCell(
      const std::vector<carl::Variable> &variableOrder,
      const RANPoint &point,
      const std::vector<Poly> &polys) {

      std::vector<TagPoly2> tPolys;
      for (const auto &poly : polys) {
        const auto polyLevel = *levelOf(variableOrder, poly);
        TagPoly2 taggedPoly = {PolyTag::SGN_INV, poly, polyLevel};
        tPolys.emplace_back(taggedPoly);
      }

      return pointEnclosingCADCell(variableOrder,point,tPolys);
    }

  std::experimental::optional<CADCell> pointEnclosingCADCell(
    const std::vector<carl::Variable> &variableOrder,
    const RANPoint &point,
    const std::vector<TagPoly2> &polys) {
    // precondition:
    assert(!variableOrder.empty());
    assert(hasUniqElems(variableOrder));
    assert(variableOrder.size() == point.dim());
    assert(hasOnlyNonConstIrreducibles(asMultiPolys(polys)));
    assert(polyVarsAreAllInList(asMultiPolys(polys), variableOrder));

    SMTRAT_LOG_INFO("smtrat.cad", "Build point enclosing CADcell");
    SMTRAT_LOG_DEBUG("smtrat.cad", "Variable order: " << variableOrder);
    SMTRAT_LOG_DEBUG("smtrat.cad", "Point: " << point);
    SMTRAT_LOG_DEBUG("smtrat.cad", "Polys: " << asMultiPolys(polys));

    CADCell cell = fullSpaceCoveringCell(point.dim());
    SMTRAT_LOG_DEBUG("smtrat.cad", "Cell: " << cell);

    carl::CoCoAAdaptor<Poly> factorizer(asMultiPolys(polys));
    const ShrinkContext ctx{point, variableOrder, factorizer};
    PolyLog emptyLog;

    for (const auto &poly : polys) {
      if (shrinkCell(ctx, emptyLog, poly, cell) == ShrinkResult::FAIL) {
        SMTRAT_LOG_WARN("smtrat.cad", "Building failed");
        return std::experimental::nullopt;
      }
    }

    SMTRAT_LOG_DEBUG("smtrat.cad", "Finished Cell: " << cell);
    return cell;
  }
};
} // namespace onecellcad
} // namespace smtrat
