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

#include <carl/core/polynomialfunctions/Derivative.h>
#include <carl/core/polynomialfunctions/Factorization.h>
#include <carl/core/polynomialfunctions/Resultant.h>

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>
#include <smtrat-cad/projectionoperator/utils.h>

#include "Assertables.h"

#include <algorithm>
#include <optional>
#include <set>
#include <unordered_map>
#include <variant>
#include <vector>

namespace smtrat {
namespace mcsat {
namespace onecellcad {

using RAN = carl::RealAlgebraicNumber<smtrat::Rational>;
using RANMap = std::map<carl::Variable, RAN>;

enum class InvarianceType {
	ORD_INV,
	SIGN_INV // order or sign invariance requirement
};

inline std::ostream& operator<<(std::ostream& os, const InvarianceType& inv) {
	switch (inv) {
	case InvarianceType::ORD_INV:
		return os << "ORD_INV";
	case InvarianceType::SIGN_INV:
		return os << "SIGN_INV";
	}
	return os;
}

/**
     * SIGN_INV < ORD_INV, since order invariance is a "stronger" property.
     */
inline bool operator<(const InvarianceType& l, const InvarianceType& r) {
	switch (l) {
	case InvarianceType::ORD_INV:
		return false;
	case InvarianceType::SIGN_INV:
		return r == InvarianceType ::ORD_INV;
	}
	return false;
}

enum class ShrinkResult {
	SUCCESS,
	FAIL
};

inline std::ostream& operator<<(std::ostream& os, const ShrinkResult& s) {
	switch (s) {
	case ShrinkResult::SUCCESS:
		return os << "SUCCESS";
	case ShrinkResult::FAIL:
		return os << "FAIL";
	}
	return os;
}

struct TagPoly2 {
	InvarianceType tag;

	Poly poly;

	/** Workaround: Cache the poly's level to avoid recomputing it in many places. */
	std::size_t level;
};

inline std::ostream& operator<<(std::ostream& os, const TagPoly2& p) {
	return os << "(poly " << p.tag << " " << p.poly << ")";
}

inline bool operator==(const TagPoly2& lhs, const TagPoly2& rhs) {
	return lhs.tag == rhs.tag && lhs.poly == rhs.poly;
}

struct TagPoly {
	InvarianceType tag;
	Poly poly;
};

inline bool operator==(const TagPoly& lhs, const TagPoly& rhs) {
	return lhs.tag == rhs.tag && lhs.poly == rhs.poly;
}

inline std::ostream& operator<<(std::ostream& os, const TagPoly& p) {
	return os << "(poly " << p.tag << " " << p.poly << ")";
}

inline std::ostream& operator<<(std::ostream& os, const std::vector<TagPoly>& polys) {
	os << "[ " << polys.size() << ": ";
	for (const auto& poly : polys)
		os << poly.tag << " " << poly.poly << ", ";
	return os << "]";
}

inline std::ostream& operator<<(std::ostream& os, const std::vector<TagPoly2>& polys) {
	os << "[ " << polys.size() << ": ";
	for (const auto& poly : polys)
		os << poly.tag << " " << poly.poly << ", ";
	return os << "]";
}

inline std::vector<Poly> asMultiPolys(const std::vector<TagPoly2> polys) {
	std::vector<Poly> mPolys;
	for (const auto& poly : polys)
		mPolys.emplace_back(poly.poly);
	return mPolys;
}

inline std::vector<Poly> asMultiPolys(const std::vector<TagPoly> polys) {
	std::vector<Poly> mPolys;
	for (const auto& poly : polys)
		mPolys.emplace_back(poly.poly);
	return mPolys;
}

inline bool contains(const std::vector<TagPoly2>& polys, const Poly& poly) {
	auto isMatch = [&poly](const TagPoly2& taggedPoly) {
		return taggedPoly.poly == poly;
	};
	return std::find_if(polys.begin(), polys.end(), isMatch) != polys.end();
}

inline bool contains(const std::vector<TagPoly>& polys, const Poly& poly) {
	auto isMatch = [&poly](const TagPoly& taggedPoly) {
		return taggedPoly.poly == poly;
	};
	return std::find_if(polys.begin(), polys.end(), isMatch) != polys.end();
}

template<typename T>
bool contains(const std::vector<T>& list, const T& elem) {
	return std::find(list.begin(), list.end(), elem) != list.end();
}

/**
     *  @param rootVariable The variable with respect to which the roots are computed in the end.
     *  It will be replaced by the special unique root-variable "_z"  common in root-expressions.
     */
inline MultivariateRootT asRootExpr(carl::Variable rootVariable, Poly poly, std::size_t rootIdx) {
	assert(poly.gatherVariables().count(rootVariable) == 1);
	// Apparently we need this complicated construction. I forgot why a simple substitute is not okay.
	return MultivariateRootT(Poly(carl::UnivariatePolynomial<Poly>(MultivariateRootT::var(),
																   poly.toUnivariatePolynomial(rootVariable).coefficients())),
							 rootIdx);
}

/**
     * Represent a cell's (closed-interval-boundary) component along th k-th axis.
     * A section is a
     * function f: algReal^{k-1} -> algReal; from a multi-dimensional input point
     * of level k-1 (whose components are algebraic reals) to an algebraic real.
     * We use a root-expression with an irreducible, multivariate polynomial of level k.
     */
struct Section {
	// A section is always finite, a sector may have infty bounds!
	MultivariateRootT boundFunction;

	/**
       * For performance we cache the isolated root from `boundFunction' that lies closest
       * along this section's level to the main point.
       */
	RAN isolatedRoot;
};

inline std::ostream& operator<<(std::ostream& os, const Section& s) {
	return os << "(section " << s.boundFunction << " " << s.isolatedRoot << ")";
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

inline std::ostream& operator<<(ostream& os, const Sector& s) {
	os << "(sector ";
	s.lowBound ? os << s.lowBound.value() : os << "-infty";
	os << " ";
	s.highBound ? os << s.highBound.value() : os << "infty";
	return os << ")";
}

/**
     * Represent a single cell [brown15].
     * A cell is a collection of boundary objects along each axis, called
     * cell-components based on math. vectors and their components.
     */
using CADCell = std::vector<std::variant<Sector, Section>>;

inline std::ostream& operator<<(ostream& os, const CADCell& cell) {
	os << "(cell [";
	for (std::size_t i = 0; i < cell.size(); i++) {
		if (std::holds_alternative<Sector>(cell[i])) {
			const auto cellSctr = std::get<Sector>(cell[i]);
			// TODO
			if (cellSctr.lowBound)
				os << cellSctr.lowBound->boundFunction;
			else
				os << "-infty";
			os << " < var_" << i << " < ";
			if (cellSctr.highBound)
				os << cellSctr.highBound->boundFunction;
			else
				os << "+infty";
		} else {
			os << "var_" << i << " = ";
			const auto cellSctn = std::get<Section>(cell[i]);
			os << cellSctn.boundFunction;
		}
		os << ", ";
	}
	return os << "])";
}

/**
     * @return Dimension of a hybercube to which the given cell is homeomorphic,
     * i.e., count the number of sectors of the given Cell restricted to its first
     * components (with index 0 to 'uptoLevel').
     */
inline std::size_t cellDimension(const CADCell& cell, const std::size_t uptoLevel) {
	std::size_t sectorCount = 0;
	for (std::size_t i = 0; i <= uptoLevel; i++)
		if (std::holds_alternative<Sector>(cell[i]))
			sectorCount++;
	return sectorCount;
}

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
inline std::optional<std::size_t> levelOf(
	const std::vector<carl::Variable>& variableOrder,
	const Poly& poly) {
	// precondition:
	assert(isSubset(asVector(poly.gatherVariables()), variableOrder));

	// Algorithm:
	// Iterate through each variable inside 'variableOrder' in ascending order
	// and remove it from 'polyVariables'. The last variable in 'polyVariables' before
	// it becomes empty is the highest appearing variable in 'poly'.

	// 'gatherVariables()' collects only variables with positive degree
	auto polyVariables = poly.gatherVariables();

	if (polyVariables.empty()) {
		return std::nullopt; // for const-polys like '2'
	}

	for (std::size_t level = 0; level < variableOrder.size(); ++level) {
		polyVariables.erase(variableOrder[level]);
		// Last variable before 'polyVariables' becomes empty is the highest variable.
		if (polyVariables.empty())
			return level;
	}
	throw("Poly contains variable not found in variableOrder");
	return std::nullopt;
}

inline CADCell fullSpaceCell(std::size_t cellComponentCount) {
	return CADCell(cellComponentCount);
}

class OneCellCAD {
private:
	/**
     * Variables can also be indexed by level. Polys with mathematical level 1 contain the variable in variableOrder[0]
     */
	const std::vector<carl::Variable>& variableOrder;
	const carl::RealAlgebraicPoint<Rational>& point;
	/**
     * Projection factor set divided into levels. Polys with mathematical level 1 are at projFactorSet[0]
     * This collection is called "P_prj" in [brown15]
     */
	std::vector<std::vector<onecellcad::TagPoly2>> projFactorSet; // init all levels with empty vector

	/** Only delinating polys. This collection is called "P_dln" in [brown15] */
	std::vector<TagPoly2> delineators;

public:
	OneCellCAD(const std::vector<carl::Variable>& variableOrder, const carl::RealAlgebraicPoint<Rational>& point)
		: variableOrder(variableOrder),
		  point(point),
		  projFactorSet(variableOrder.size()), // that many levels exist
		  delineators() {
		// precondition:
		assert(!variableOrder.empty());
		assert(hasUniqElems(variableOrder));
		assert(variableOrder.size() == point.dim());
	}

	/**
     * Create a mapping from the first variables (with index 0 to 'componentCount') in the
     * 'variableOrder' to the first components of the given 'point'.
     */
	std::map<carl::Variable, RAN> prefixPointToStdMap(
		const std::size_t componentCount) {
		std::map<carl::Variable, RAN> varToRANMap;
		for (std::size_t i = 0; i < componentCount; i++)
			varToRANMap[variableOrder[i]] = point[i];
		return varToRANMap;
	}

	/**src/lib/datastructures/mcsat/onecellcad/OneCellCAD.h
     * Given a poly p(x1,..,xn), return all roots of the univariate poly
     * p(a1,..,an-1, xn), where a1,..an-1 are the first algebraic real components
     * from 'point'.
     */
	std::vector<RAN> isolateLastVariableRoots(
		const std::size_t polyLevel,
		const Poly& poly) {
		// 'realRoots' returns std::nullopt if poly vanishes
		// early, but here we don't care
		return carl::rootfinder::realRoots(
			poly.toUnivariatePolynomial(variableOrder[polyLevel]),
			prefixPointToStdMap(polyLevel));
	}

	bool isAlreadyProcessed(const TagPoly2& poly) {
		// matches if poly is found with its tag or an oi-tag
		auto isMatch = [&poly](const TagPoly2& processedPoly) {
			return processedPoly.poly == poly.poly &&
				   (processedPoly.tag == poly.tag || processedPoly.tag == InvarianceType::ORD_INV);
		};
		auto& log = projFactorSet[poly.level];
		if (std::find_if(log.begin(), log.end(), isMatch) != log.end())
			return true;

		return std::find_if(delineators.begin(), delineators.end(), isMatch) != delineators.end();
	}

	/**
     * Check if an n-variate 'poly' p(x1,..,xn) with n>=1 already becomes the
     * zero poly after plugging in p(a1,..,an-1, xn), where a1,..an-1 are the
     * first n-1 algebraic real components from 'point'.
     */
	inline bool vanishesEarly(
		const std::size_t polyLevel,
		const Poly& poly) {
		// precondition:
		assert(!poly.isConstant());
		if (poly.isLinear())
			return false; // cannot vanish early

		const carl::Variable mainVariable = variableOrder[polyLevel];
		std::map<carl::Variable, carl::Interval<Rational>> dummy;
		auto resultPoly =
			carl::RealAlgebraicNumberEvaluation::evaluateCoefficients(
				poly.toUnivariatePolynomial(mainVariable),
				prefixPointToStdMap(polyLevel),
				dummy);
		return carl::isZero(resultPoly);
	}

	bool isPointRootOfPoly(
		const std::size_t polyLevel,
		const Poly& poly) {
		const std::size_t componentCount = polyLevel + 1;
		std::vector<carl::Variable> subVariableOrder(
			variableOrder.begin(),
			variableOrder.begin() + (long)componentCount);
		// 'evaluate' only accepts a point and variables with exactly
		// 'componentCount' number of components
		RAN result = carl::RealAlgebraicNumberEvaluation::evaluate(
			poly,
			point.prefixPoint(componentCount),
			subVariableOrder);
		return result.isZero();
	}

	inline bool isPointRootOfPoly(
		const TagPoly2& poly) {
		return isPointRootOfPoly(poly.level, poly.poly);
	}

	bool isPointInsideCell(
		const CADCell& cell) {
		// precondition
		assert(point.dim() >= 1);
		assert(cell.size() == point.dim());

		for (std::size_t level = 0; level < point.dim(); level++) {
			const carl::Variable lvlVar = variableOrder[level];
			if (std::holds_alternative<Section>(cell[level])) {
				const Section section = std::get<Section>(cell[level]);
				if (!isPointRootOfPoly(level, section.boundFunction.poly(lvlVar)))
					return false;
				if (section.isolatedRoot != point[level])
					return false;
			} else {
				const Sector sector = std::get<Sector>(cell[level]);
				if (sector.highBound) {
					const Section highBound = *sector.highBound;
					if (point[level] > highBound.isolatedRoot)
						return false;
					if (!isSubset(
							std::vector<RAN>{highBound.isolatedRoot},
							isolateLastVariableRoots(level, highBound.boundFunction.poly(lvlVar)))) {
						return false;
					}
				}
				if (sector.lowBound) {
					const Section lowBound = *sector.lowBound;
					if (point[level] < lowBound.isolatedRoot)
						return false;
					if (!isSubset(
							std::vector<RAN>{lowBound.isolatedRoot},
							isolateLastVariableRoots(level, lowBound.boundFunction.poly(lvlVar)))) {
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
		const std::size_t polyLevel,
		const Poly& poly,
		CADCell& cell) {
		// This function is called "Update" in [brown15]
		// precondition:
		assert(isNonConstIrreducible(poly));
		assert(!vanishesEarly(polyLevel, poly));
		if (std::holds_alternative<Section>(cell[polyLevel]))
			return; // canot shrink further

		Sector& sector = std::get<Sector>(cell[polyLevel]);
		const RAN pointComp = point[polyLevel]; // called alpha_k in [brown15]

		SMTRAT_LOG_DEBUG("smtrat.cad", "Shrink cell sector at lvl " << polyLevel);
		SMTRAT_LOG_TRACE("smtrat.cad", "Sector: " << sector);
		SMTRAT_LOG_TRACE("smtrat.cad", "Poly: " << poly);
		SMTRAT_LOG_TRACE("smtrat.cad", "Lvl-Var: " << variableOrder[polyLevel]);
		SMTRAT_LOG_DEBUG("smtrat.cad", "PointComp: " << pointComp);
		//SMTRAT_LOG_TRACE("smtrat.cad", "Point: " << point.prefixPoint(polyLevel + 1));
		// Isolate real isolatedRoots of level-k 'poly' after plugin in a level-(k-1) point.
		// Poly must not vanish under this prefixPoint!
		auto isolatedRoots =
			isolateLastVariableRoots(polyLevel, poly);
		if (isolatedRoots.empty()) {
			SMTRAT_LOG_TRACE("smtrat.cad", "No isolatable isolatedRoots");
			return;
		}
		SMTRAT_LOG_TRACE("smtrat.cad", "Isolated roots: " << isolatedRoots);

		if (sector.lowBound) {
			SMTRAT_LOG_TRACE("smtrat.cad", "Existing low bound: " << (*(sector.lowBound)).isolatedRoot);
			assert((*(sector.lowBound)).isolatedRoot < pointComp);
		}
		if (sector.highBound) {
			SMTRAT_LOG_TRACE("smtrat.cad", "Existing high bound: " << (*(sector.highBound)).isolatedRoot);
			assert((*(sector.highBound)).isolatedRoot > pointComp);
		}

		// Search for closest isolatedRoots/boundPoints to pointComp, i.e.
		// someRoot ... < closestLower <= pointComp <= closestUpper < ... someOtherRoot
		std::optional<RAN> closestLower;
		std::optional<RAN> closestUpper;

		std::size_t rootIdx = 0, lowerRootIdx, upperRootIdx;
		carl::Variable rootVariable = variableOrder[polyLevel];
		for (const auto& root : isolatedRoots) {
			rootIdx++;
			if (root < pointComp) {
				SMTRAT_LOG_TRACE("smtrat.cad", "Smaller: " << root);
				if (!closestLower || *closestLower < root) {
					closestLower = root;
					lowerRootIdx = rootIdx;
				}
			} else if (root == pointComp) {
				SMTRAT_LOG_TRACE("smtrat.cad", "Equal: " << root);
				// Sector collapses into a section
				cell[polyLevel] = Section{asRootExpr(rootVariable, poly, rootIdx), root};
				SMTRAT_LOG_TRACE("smtrat.cad", "Sector collapses: " << (Section{asRootExpr(rootVariable, poly, rootIdx), root}));
				return;
			} else { // pointComp < root
				SMTRAT_LOG_TRACE("smtrat.cad", "Bigger: " << root);
				if (!closestUpper || root < *closestUpper) {
					closestUpper = root;
					upperRootIdx = rootIdx;
				}
			}
		}

		if (closestLower) {
			if (!sector.lowBound || (*(sector.lowBound)).isolatedRoot < closestLower) {
				sector.lowBound = Section{asRootExpr(rootVariable, poly, lowerRootIdx), *closestLower};
				SMTRAT_LOG_TRACE("smtrat.cad", "New section: "
												   << " " << sector);
			}
		}

		if (closestUpper) {
			if (!sector.highBound || closestUpper < (*(sector.highBound)).isolatedRoot) {
				sector.highBound = Section{asRootExpr(rootVariable, poly, upperRootIdx), *closestUpper};
				SMTRAT_LOG_TRACE("smtrat.cad", "New section: "
												   << " " << sector);
			}
		}
	}

	/**
     * Find the smallest index m such that in the set S of all m-th partial
     * derivatives of the given poly, such that there is a derivative that does
     * not vanish early [brown15].
     * Note that m > 0 i.e, this function never just returns the given poly,
     * which is the 0th partial derivative of itself.
     * @param poly must not be a const-poly like 2, otherwise this function
     * does not terminate.
     * @return Actually only returns the set S
     */
	std::vector<Poly> partialDerivativesLayerWithSomeNonEarlyVanishingPoly(
		const std::vector<carl::Variable>& variableOrder,
		const carl::RealAlgebraicPoint<Rational>& point,
		const TagPoly2& mainPoly) {
		assert(!mainPoly.poly.isConstant());
		// We search for this set of partial derivatives "layer by layer".
		// The layer of 0-th partial derivatives is the mainPoly itself.
		std::vector<Poly> layerOfDerivatives;
		layerOfDerivatives.emplace_back(mainPoly.poly);
		bool foundSomeNonEarlyVanishingDerivative = false;

		do {
			std::vector<Poly> nextLayer;
			for (const auto& poly : layerOfDerivatives) {
				// Derive poly wrt to each variable (variables with idx 0 to 'mainPoly.level')
				for (std::size_t varIdx = 0; varIdx <= mainPoly.level; varIdx++) {
					const auto derivative = carl::derivative(poly, variableOrder[varIdx]);
					if (carl::isZero(derivative))
						continue;
					nextLayer.emplace_back(derivative);
					if (foundSomeNonEarlyVanishingDerivative)
						continue; // avoid expensive vanishing check

					if (derivative.isConstant() ||
						!vanishesEarly(mainPoly.level, mainPoly.poly))
						foundSomeNonEarlyVanishingDerivative = true;
					// still need to compute all remaining nextLayer-polys
				}
			}
			layerOfDerivatives = std::move(nextLayer);
		} while (!foundSomeNonEarlyVanishingDerivative);

		return layerOfDerivatives;
	}

	inline Poly discriminant(const carl::Variable& mainVariable, const Poly& p) {
		return Poly(carl::discriminant(p.toUnivariatePolynomial(mainVariable)));
	}

	ShrinkResult refineNull(
		const TagPoly2& boundCandidate,
		CADCell& cell) {
		// This function is called "RefNull" in [brown15]
		// precondition:
		assert(isNonConstIrreducible(boundCandidate.poly));
		assert(isPointRootOfPoly(boundCandidate));
		SMTRAT_LOG_TRACE("smtrat.cad", "RefineNull");
		const auto mainVariable = variableOrder[boundCandidate.level];
		const auto boundCandidateUniPoly =
			boundCandidate.poly.toUnivariatePolynomial(mainVariable);
		std::vector<TagPoly2> projectionResult;

		projectionResult.emplace_back(TagPoly2{
			InvarianceType::ORD_INV,
			discriminant(mainVariable, boundCandidate.poly),
			0}); // hack: we compute the level later in this function

		projectionResult.emplace_back(TagPoly2{
			InvarianceType::ORD_INV,
			boundCandidateUniPoly.lcoeff(),
			0}); // hack: we compute the level later in this function

		projectionResult.emplace_back(TagPoly2{
			InvarianceType::ORD_INV,
			boundCandidateUniPoly.tcoeff(),
			0}); // hack: we compute the level later in this function

		for (auto& resultPoly : projectionResult) {
			if (resultPoly.poly.isConstant())
				continue;

			// Hack: add the correct level here
			resultPoly.level = *levelOf(variableOrder, resultPoly.poly);
			if (shrinkCellWithIrreducibleFactorsOfPoly(resultPoly, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;
		}

		return ShrinkResult::SUCCESS;
	}

	ShrinkResult shrinkCellWithEarlyVanishingPoly(
		const TagPoly2& boundCandidate,
		CADCell& cell) {
		// This function is called MergeNull in [brown15]
		// precondition:
		assert(vanishesEarly(boundCandidate.level, boundCandidate.poly));
		assert(isNonConstIrreducible(boundCandidate.poly));
		SMTRAT_LOG_TRACE("smtrat.cad", "ShrinkWithEarlyVanishingPoly");

		auto shrinkResult = refineNull(boundCandidate, cell);
		if (shrinkResult == ShrinkResult::FAIL)
			return shrinkResult;

		if (boundCandidate.tag == InvarianceType::SIGN_INV) {
			projFactorSet[boundCandidate.level].emplace_back(boundCandidate);
			return ShrinkResult::SUCCESS;
		} else { //boundCandidate.tag == InvarianceType::ORD_INV
			if (cellDimension(cell, boundCandidate.level - 1) > 0)
				return ShrinkResult::FAIL;

			// Construct a delineating poly as the sum of all non-earlyVanishing,
			// squared m-th partial derivatives.
			Poly delineator(0);
			for (const auto& poly :
				 partialDerivativesLayerWithSomeNonEarlyVanishingPoly(
					 variableOrder, point, boundCandidate)) {
				if (!vanishesEarly(boundCandidate.level, boundCandidate.poly))
					delineator += poly * poly;
			}

			if (!delineator.isConstant()) {
				const std::size_t delineatorLevel = *levelOf(variableOrder, delineator);
				shrinkSingleComponent(delineatorLevel, delineator, cell);

				const TagPoly2 taggedDelineator{
					InvarianceType::ORD_INV,
					delineator,
					delineatorLevel};
				projFactorSet[delineatorLevel].emplace_back(taggedDelineator);
				delineators.emplace_back(taggedDelineator);
			}
			return ShrinkResult::SUCCESS;
		}
	}

	/** Compute the resultant of two multivariate polynomials wrt. a given 'mainVariable' */
	inline Poly resultant(const carl::Variable& mainVariable, const Poly& p1, const Poly& p2) {
		const auto p1UPoly = p1.toUnivariatePolynomial(mainVariable);
		const auto p2UPoly = p2.toUnivariatePolynomial(mainVariable);
		return Poly(carl::resultant(p1UPoly, p2UPoly));
	}

	ShrinkResult shrinkCellWithIrreducibleFactorsOfPoly(
		const TagPoly2& poly,
		CADCell& cell) {
		for (const auto& factor : carl::irreducibleFactors(poly.poly, false)) {
			SMTRAT_LOG_TRACE("smtrat.cad", "Shrink with irreducible factor: Poly: "
											   << poly.poly << " Factor: " << factor);
			if (factor.isConstant())
				continue;

			const std::size_t factorLevel = *levelOf(variableOrder, factor);
			TagPoly2 factorWithInheritedTag{poly.tag, factor, factorLevel};
			if (shrinkCell(factorWithInheritedTag, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;
		}
		return ShrinkResult::SUCCESS;
	}

	ShrinkResult refineNonNull(
		const TagPoly2& boundCandidate,
		CADCell& cell) {
		// This function is called "RefNonNull" in [brown15]
		// precondition:
		assert(isNonConstIrreducible(boundCandidate.poly));
		assert(!vanishesEarly(boundCandidate.level, boundCandidate.poly));
		SMTRAT_LOG_TRACE("smtrat.cad", "RefineNonNull");

		const auto mainVariable = variableOrder[boundCandidate.level];
		const auto boundCandidateUniPoly =
			boundCandidate.poly.toUnivariatePolynomial(mainVariable);

		// Do early-exit tests:
		for (const auto& coeff : boundCandidateUniPoly.coefficients()) {
			if (coeff.isConstant() && !carl::isZero(coeff))
				return ShrinkResult::SUCCESS;
		}

		const auto& leadCoeff = boundCandidate.poly.lcoeff(mainVariable);
		const auto leadCoeffLvl = levelOf(variableOrder, leadCoeff);
		if (!leadCoeff.isConstant() && (contains(projFactorSet[*leadCoeffLvl], leadCoeff) || contains(delineators, leadCoeff)) && !isPointRootOfPoly(*leadCoeffLvl, leadCoeff)) {
			return ShrinkResult::SUCCESS;
		}

		const auto discrim = discriminant(mainVariable, boundCandidate.poly);
		const auto discrimLvl = levelOf(variableOrder, discrim);
		if (!discrim.isConstant() && (contains(projFactorSet[*discrimLvl], discrim) || contains(delineators, discrim)) && !isPointRootOfPoly(*discrimLvl, discrim)) {
			return ShrinkResult::SUCCESS;
		}

		// optional early-exit check: if for every point in subcell, poly does not
		// vanish, return success. No idea how to do that efficiently.

		for (const auto& coeff : boundCandidateUniPoly.coefficients()) {
			// find first non-vanishing coefficient:
			const auto coeffLevel = *levelOf(variableOrder, coeff); // certainly non-constant
			if (!isPointRootOfPoly(coeffLevel, coeff)) {
				return shrinkCellWithIrreducibleFactorsOfPoly(
					{InvarianceType::SIGN_INV, coeff, coeffLevel},
					cell);
			}
		}
		return ShrinkResult::SUCCESS;
	}

	ShrinkResult shrinkCellWithPolyHavingPointAsRoot(
		const TagPoly2& boundCandidate,
		CADCell& cell) {
		// This function is called MergeRoot in [brown15]
		// precondition:
		assert(!vanishesEarly(boundCandidate.level, boundCandidate.poly));
		assert(isPointRootOfPoly(boundCandidate));
		SMTRAT_LOG_TRACE("smtrat.cad", "ShrinkWithPolyHavingPointAsRoot");

		// Do a "model-based" Brown-McCallum projection.
		std::vector<TagPoly2> projectionResult;
		const auto mainVariable = variableOrder[boundCandidate.level];
		if (std::holds_alternative<Section>(cell[boundCandidate.level])) {
			projectionResult.emplace_back(TagPoly2{
				InvarianceType::ORD_INV,
				resultant(
					mainVariable,
					boundCandidate.poly,
					std::get<Section>(cell[boundCandidate.level]).boundFunction.poly(mainVariable)),
				0}); // hack: we compute the level later in this function

			if (boundCandidate.tag == InvarianceType::ORD_INV) {
				projectionResult.emplace_back(TagPoly2{
					InvarianceType::SIGN_INV,
					boundCandidate.poly.lcoeff(mainVariable),
					0}); // hack: we compute the level later in this function
				projectionResult.emplace_back(TagPoly2{
					InvarianceType::ORD_INV,
					discriminant(mainVariable, boundCandidate.poly),
					0}); // hack: we compute the level later in this function
			}
		} else { // cellComponent is a Sector at 'boundCandidate's level
			projectionResult.emplace_back(TagPoly2{
				InvarianceType::SIGN_INV,
				boundCandidate.poly.lcoeff(mainVariable),
				0}); // hack: we compute the level later in this function
			projectionResult.emplace_back(TagPoly2{
				InvarianceType::ORD_INV,
				discriminant(mainVariable, boundCandidate.poly),
				0}); // hack: we compute the level later in this function

			Sector& sectorAtLvl = std::get<Sector>(cell[boundCandidate.level]);

			if (sectorAtLvl.lowBound) {
				projectionResult.emplace_back(TagPoly2{
					InvarianceType::ORD_INV,
					resultant(
						mainVariable,
						boundCandidate.poly,
						sectorAtLvl.lowBound->boundFunction.poly(mainVariable)),
					0}); // hack: we compute the level later in this function
			}
			if (sectorAtLvl.highBound) {
				projectionResult.emplace_back(TagPoly2{
					InvarianceType::ORD_INV,
					resultant(
						mainVariable,
						boundCandidate.poly,
						sectorAtLvl.highBound->boundFunction.poly(mainVariable)),
					0}); // hack: we compute the level later in this function
			}
		}

		for (auto& resultPoly : projectionResult) {
			if (resultPoly.poly.isConstant())
				continue;
			// Hack: add the correct level here
			resultPoly.level = *levelOf(variableOrder, resultPoly.poly);

			if (shrinkCellWithIrreducibleFactorsOfPoly(resultPoly, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;
		}

		if (boundCandidate.tag == InvarianceType::ORD_INV ||
			std::holds_alternative<Sector>(cell[boundCandidate.level])) {
			if (refineNonNull(boundCandidate, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;

			shrinkSingleComponent(boundCandidate.level, boundCandidate.poly, cell);
		}

		projFactorSet[boundCandidate.level].emplace_back(TagPoly2{
			InvarianceType::SIGN_INV,
			boundCandidate.poly,
			boundCandidate.level});

		return ShrinkResult::SUCCESS;
	}

	/** Check if there is a root of the given polynomial---that becomes univariate
     * after pluggin in all but the last variable wrt. the given variableOrder---,
     * that lies between the given 'low' and 'high' bounds.
     */
	bool hasPolyLastVariableRootWithinBounds(
		const RAN& low,
		const RAN& high,
		const Poly& poly,
		const std::size_t polyLevel) {
		for (const RAN& candidate :
			 isolateLastVariableRoots(polyLevel, poly)) {
			if (low <= candidate && candidate <= high)
				return true;
		}
		return false;
	}

	ShrinkResult shrinkCellWithNonRootPoint(
		const TagPoly2& boundCandidate,
		CADCell& cell) {
		// This function is called "MergeNotRoot" in [brown15]
		// precondition:
		assert(isNonConstIrreducible(boundCandidate.poly));
		assert(!isPointRootOfPoly(boundCandidate));
		SMTRAT_LOG_TRACE("smtrat.cad", "ShrinkWithNonRootPoint");

		// Do a "model-based" Brown-McCallum projection.
		std::vector<TagPoly2> projectionResult;
		const auto mainVariable = variableOrder[boundCandidate.level];
		if (std::holds_alternative<Section>(cell[boundCandidate.level])) {
			Section sectionAtLvl = std::get<Section>(cell[boundCandidate.level]);
			projectionResult.emplace_back(TagPoly2{
				InvarianceType::ORD_INV,
				resultant(mainVariable, boundCandidate.poly, sectionAtLvl.boundFunction.poly(mainVariable)),
				0}); // hack: we compute the level later in this function});
		} else {	 // cellComponent is a Sector at 'boundCandidate's level
			projectionResult.emplace_back(TagPoly2{
				InvarianceType::ORD_INV,
				discriminant(mainVariable, boundCandidate.poly),
				0}); // hack: we compute the level later in this function});

			Sector sectorAtLvl = std::get<Sector>(cell[boundCandidate.level]);
			if (!sectorAtLvl.lowBound || !sectorAtLvl.highBound ||
				hasPolyLastVariableRootWithinBounds(
					sectorAtLvl.lowBound->isolatedRoot,
					sectorAtLvl.highBound->isolatedRoot,
					boundCandidate.poly,
					boundCandidate.level)) {
				projectionResult.emplace_back(TagPoly2{
					InvarianceType::SIGN_INV,
					boundCandidate.poly.lcoeff(mainVariable),
					0}); // hack: we compute the level later in this function});
			}

			if (sectorAtLvl.lowBound) {
				projectionResult.emplace_back(TagPoly2{
					InvarianceType::ORD_INV,
					resultant(
						mainVariable,
						boundCandidate.poly,
						sectorAtLvl.lowBound->boundFunction.poly(mainVariable)),
					0}); // hack: we compute the level later in this function});
			}
			if (sectorAtLvl.highBound) {
				projectionResult.emplace_back(TagPoly2{
					InvarianceType::ORD_INV,
					resultant(
						mainVariable,
						boundCandidate.poly,
						sectorAtLvl.highBound->boundFunction.poly(mainVariable)),
					0}); // hack: we compute the level later in this function});
			}
		}

		for (auto resultPoly : projectionResult) {
			if (resultPoly.poly.isConstant())
				continue;

			// Hack: add the correct level here
			resultPoly.level = *levelOf(variableOrder, resultPoly.poly);
			if (shrinkCellWithIrreducibleFactorsOfPoly(resultPoly, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;
		}

		if (std::holds_alternative<Sector>(cell[boundCandidate.level])) {
			if (refineNonNull(boundCandidate, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;

			shrinkSingleComponent(boundCandidate.level, boundCandidate.poly, cell);
		}

		projFactorSet[boundCandidate.level].emplace_back(TagPoly2{
			InvarianceType::SIGN_INV,
			boundCandidate.poly,
			boundCandidate.level});

		return ShrinkResult::SUCCESS;
	}

	/**
     * Merge the given open OpenCADCell 'cell' that contains the given 'point'
     * (called "alpha" in [brown15]) with a polynomial 'poly'.
     * Before the merge 'cell' represents a region that is sign-invariant
     * on other (previously merged) polynomials (all signs are non-zero).
     * The returned cell represents a region that is additionally sign-invariant on
     * 'poly' (also with non-zero sign).
     * @return either an OpenCADCell or nothing (representing a failed construction)
     */
	ShrinkResult shrinkCell(
		const TagPoly2& boundCandidate,
		CADCell& cell) {
		// This function is called "Merge" in [brown15]
		// precondition:
		assert(isPointInsideCell(cell));

		SMTRAT_LOG_INFO("smtrat.cad", "Shrink cell");
		SMTRAT_LOG_DEBUG("smtrat.cad", "Poly: " << boundCandidate);
		SMTRAT_LOG_DEBUG("smtrat.cad", "Cell: " << cell);

		if (isAlreadyProcessed(boundCandidate))
			return ShrinkResult::SUCCESS;

		if (cellDimension(cell, boundCandidate.level) == 0) {
			projFactorSet[boundCandidate.level].emplace_back(TagPoly2{InvarianceType::ORD_INV, boundCandidate.poly, boundCandidate.level});
			return ShrinkResult::SUCCESS;
		}

		if (boundCandidate.level == 0) {
			if (std::holds_alternative<Sector>(cell[boundCandidate.level]))
				shrinkSingleComponent(boundCandidate.level, boundCandidate.poly, cell);
			projFactorSet[boundCandidate.level].emplace_back(TagPoly2{InvarianceType::ORD_INV, boundCandidate.poly, boundCandidate.level});
			return ShrinkResult::SUCCESS;
		}

		if (vanishesEarly(boundCandidate.level, boundCandidate.poly))
			return shrinkCellWithEarlyVanishingPoly(boundCandidate, cell);

		// lower level subcell
		if (cellDimension(cell, boundCandidate.level - 1) == 0) {
			shrinkSingleComponent(boundCandidate.level, boundCandidate.poly, cell);
			projFactorSet[boundCandidate.level].emplace_back(TagPoly2{InvarianceType::ORD_INV, boundCandidate.poly, boundCandidate.level});
			return ShrinkResult::SUCCESS;
		}

		if (isPointRootOfPoly(boundCandidate))
			return shrinkCellWithPolyHavingPointAsRoot(boundCandidate, cell);
		else
			return shrinkCellWithNonRootPoint(boundCandidate, cell);
	}

	bool isMainPointInsideCell(const CADCell& cell) {
		for (std::size_t lvl = 0; lvl < cell.size(); lvl++) {
			const RAN pointCmp = point[lvl];
			const auto cellCmp = cell[lvl];
			if (std::holds_alternative<Sector>(cellCmp)) {
				// must be low <  point_k < high
				const auto cellSctr = std::get<Sector>(cellCmp);
				if (cellSctr.lowBound) {
					if (!(cellSctr.lowBound->isolatedRoot < pointCmp))
						return false;
				}
				if (cellSctr.highBound) {
					if (!(cellSctr.highBound->isolatedRoot > pointCmp))
						return false;
				}
			} else {
				const auto cellSctn = std::get<Section>(cellCmp);
				// must be point_k == root
				SMTRAT_LOG_DEBUG("smtrat.cad", "##Section: " << cellSctn << " point_" << lvl << ": " << pointCmp);
				if (!(cellSctn.isolatedRoot == pointCmp))
					return false;
			}
		}
		return true;
	}

	std::optional<CADCell> createCADCellAroundPoint(
		const std::vector<Poly>& polys) {
		// precondition:
		assert(hasOnlyNonConstIrreducibles(polys));
		assert(polyVarsAreAllInList(polys, variableOrder));

		SMTRAT_LOG_INFO("smtrat.cad", "Build CADcell around point");
		SMTRAT_LOG_DEBUG("smtrat.cad", "Variable order: " << variableOrder);
		SMTRAT_LOG_DEBUG("smtrat.cad", "Point: " << point);
		SMTRAT_LOG_DEBUG("smtrat.cad", "Polys: " << polys);

		CADCell cell = fullSpaceCell(point.dim());
		SMTRAT_LOG_DEBUG("smtrat.cad", "Cell: " << cell);

		for (const auto& poly : polys) {
			auto level = levelOf(variableOrder, poly);
			if (shrinkCell(TagPoly2{InvarianceType::SIGN_INV, poly, *level}, cell) == ShrinkResult::FAIL) {
				SMTRAT_LOG_WARN("smtrat.cad", "Building failed");
				return std::nullopt;
			}
		}

		SMTRAT_LOG_DEBUG("smtrat.cad", "Finished Cell: " << cell);
		assert(isMainPointInsideCell(cell));
		return cell;
	}

	std::optional<CADCell> pointEnclosingCADCell(
		const std::vector<TagPoly2>& polys) {
		// precondition:
		assert(hasOnlyNonConstIrreducibles(asMultiPolys(polys)));
		assert(polyVarsAreAllInList(asMultiPolys(polys), variableOrder));

		SMTRAT_LOG_INFO("smtrat.cad", "Build point enclosing CADcell");
		SMTRAT_LOG_DEBUG("smtrat.cad", "Variable order: " << variableOrder);
		SMTRAT_LOG_DEBUG("smtrat.cad", "Point: " << point);
		SMTRAT_LOG_DEBUG("smtrat.cad", "Polys: " << asMultiPolys(polys));

		CADCell cell = fullSpaceCell(point.dim());
		SMTRAT_LOG_DEBUG("smtrat.cad", "Cell: " << cell);

		for (const auto& poly : polys) {
			if (shrinkCell(poly, cell) == ShrinkResult::FAIL) {
				SMTRAT_LOG_WARN("smtrat.cad", "Building failed");
				return std::nullopt;
			}
		}

		SMTRAT_LOG_DEBUG("smtrat.cad", "Finished Cell: " << cell);
		assert(isMainPointInsideCell(cell));
		return cell;
	}

	/**
      * Construct a single CADCell that contains the given 'point' and is
      * sign-invariant for the given polynomials in 'polys'.  The construction
      * fails if 'polys' are not well-oriented [mccallum84].  Note that
      * this cell is cylindrical only with respect to the given 'variableOrder'.
      *
      * @param variableOrder must contain unique variables and at least one,
      * because constant polynomials (without a variable) are prohibited.
      * @param point point.size() >= variables.size().
      * @param polys must contain only non-constant, irreducible polynomials that
      * mention only variables that appear in 'variableOrder'.
      *
      */
	std::optional<CADCell> pointEnclosingCADCell(
		const std::vector<Poly>& polys) {

		std::vector<TagPoly2> tPolys;
		for (const auto& poly : polys) {
			const auto polyLevel = *levelOf(variableOrder, poly);
			TagPoly2 taggedPoly = {InvarianceType::SIGN_INV, poly, polyLevel};
			tPolys.emplace_back(taggedPoly);
		}

		return pointEnclosingCADCell(tPolys);
	}
};

inline std::vector<TagPoly> singleLevelFullProjection(
	carl::Variable mainVar,
	carl::Variable sndMainVar, //workaround for projection::normalize/discrimant functions
	std::vector<TagPoly> polys) {

	SMTRAT_LOG_DEBUG("smtrat.cad", "Do full McCallum projection of " << polys);
	std::vector<TagPoly> projectionResult;
	for (std::size_t i = 0; i < polys.size(); i++) {
		auto poly1 = polys[i].poly.toUnivariatePolynomial(mainVar);
		for (const auto& coeff : poly1.coefficients()) {
			if (coeff.isConstant()) continue;
			//            SMTRAT_LOG_DEBUG("smtrat.cad", " " << coeff);
			projectionResult.emplace_back(TagPoly{InvarianceType ::SIGN_INV, Poly(smtrat::cad::projection::normalize(coeff.toUnivariatePolynomial(sndMainVar)))});
		}
		//      Poly leadCoeff =
		//        Poly(smtrat::cad::projection::normalize(poly1.lcoeff().toUnivariatePolynomial(sndMainVar)));
		//      if (!leadCoeff.isConstant())
		//        projectionResult.emplace_back(TagPoly{InvarianceType::SIGN_INV, leadCoeff});
		Poly discr =
			Poly(smtrat::cad::projection::discriminant(sndMainVar, poly1)); // already normalizes
		if (!discr.isConstant())
			projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, discr});
		for (std::size_t j = i + 1; j < polys.size(); j++) {
			auto poly2 = polys[j].poly.toUnivariatePolynomial(mainVar);
			Poly res =
				Poly(smtrat::cad::projection::resultant(sndMainVar, poly1, poly2)); // already normalizes
			if (!res.isConstant())
				projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, res});
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.cad", "Result of projection of " << projectionResult);
	return projectionResult;
}

inline std::vector<TagPoly> nonConstIrreducibleFactors(
	std::vector<TagPoly> polys) {

	std::vector<TagPoly> factors;
	for (auto& poly : polys) {
		for (const auto& factor : carl::irreducibleFactors(poly.poly, false))
			factors.emplace_back(TagPoly{poly.tag, factor}); // inherit poly's tag
	}
	return factors;
}

inline void categorizeByLevel(
	std::vector<std::vector<TagPoly>>& projectionLevels, // output argument
	const std::vector<carl::Variable>& varOrder,
	const std::vector<TagPoly>& polys) { // constant-polys prohibited

	//assert(enough Levels for polys)
	for (const auto& poly : polys) {
		if (poly.poly.isNumber()) continue;
		auto level = levelOf(varOrder, poly.poly);
		assert(level.has_value());
		assert(*level < projectionLevels.size());
		projectionLevels[*level].emplace_back(poly);
	}
}

} // namespace onecellcad
} // namespace mcsat
} // namespace smtrat
