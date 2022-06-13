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

#include <algorithm>
#include <optional>
#include <set>
#include <unordered_map>
#include <vector>

#include <carl-arith/converter/CoCoAAdaptor.h>
#include <carl-arith/poly/umvpoly/MultivariatePolynomial.h>
#include <carl-arith/poly/umvpoly/functions/Resultant.h>
#include <carl-arith/poly/umvpoly/UnivariatePolynomial.h>
#include <carl-arith/core/Variable.h>
#include <carl-arith/core/VariablePool.h>
#include <carl-arith/ran/real_roots.h>
#include <carl-arith/ran/ran.h>
#include <carl-arith/ran/RealAlgebraicPoint.h>

#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace onecellcad {
namespace recursive {

using UniPoly = carl::UnivariatePolynomial<smtrat::Rational>;
using MultiPoly = carl::MultivariatePolynomial<smtrat::Rational>;
using MultiCoeffUniPoly = carl::UnivariatePolynomial<MultiPoly>;
using RAN = carl::RealAlgebraicNumber<smtrat::Rational>;
using RANPoint = RealAlgebraicPoint<smtrat::Rational>;
using RANMap = std::map<carl::Variable, RAN>;

/**
   * Represent a cell's closed-interval-boundary object along one single axis by an
   * irreducible, multivariate polynomial of level k.
   * A section is an algebraic/"moving" boundary, because it's basically a
   * function f: algReal^{k-1} -> algReal; from a multi-dimensional input point
   * of level k-1 (whose components are algebraic reals) to an algebraic real
   * (the bound along k-th axis that changes depending on the input point).
   */
struct Section {
	MultiPoly poly;

	/**
     * A single, special bound after having plugged a specific point of level k-1
     * can be cached for performance (needed for [1]).
     */
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
	std::optional<Section> lowBound;

	std::optional<Section> highBound;

	bool isLowBoundNegInfty() const {
		return lowBound == std::nullopt;
	}

	bool isHighBoundInfty() const {
		return highBound == std::nullopt;
	}
};

std::ostream& operator<<(std::ostream& o, const Sector& s) {
	o << "(sector (low ";
	s.isLowBoundNegInfty() ? o << "-infty) " : o << s.lowBound.value() << ") ";
	o << "(high ";
	s.isHighBoundInfty() ? o << "infty)" : o << s.highBound.value() << ")";
	return o << ")";
}

/**
   * Represent a single open cell [1].
   * A cell is a collection of boundary objects along each axis.
   * In case of an open cell, the boundary objects are all sectors.
   */
using OpenCADCell = std::vector<Sector>;

std::ostream& operator<<(std::ostream& o, const OpenCADCell& c) {
	o << "(cell (level " << c.size() << ") ";
	for (auto& sector : c) {
		o << sector << " ";
	}
	return o << ")";
}

OpenCADCell createFullspaceCoveringCell(size_t level) {
	return OpenCADCell(level);
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
   * - 'variables(poly)' must be a subset of 'variableOrder'.
   */
size_t levelOf(const MultiPoly& poly,
			   const std::vector<carl::Variable>& variableOrder) {
	// 'variables()' collects only vars with positive degree
	std::set<carl::Variable> polyVarSet = carl::variables(poly).as_set();
	// Algorithm:
	// Iterate through each variable inside 'variableOrder' in ascending order
	// and remove it from 'polyVarSet'. The last variable in 'polyVarSet' before
	// it becomes empty is the highest appearing variable in 'poly'.

	if (polyVarSet.empty())
		return 0; // for const-polys like '2'

	size_t level = 1;
	for (const auto& var : variableOrder) {
		polyVarSet.erase(var);
		// Last variable before 'polyVars' becomes empty is the highest variable.
		if (polyVarSet.empty()) {
			return level;
		}
		level++;
	}
	assert(false); // Should never be reached
	return 0;
}

/**
   * Create a mapping from the first 'count'-many variables in the given
   * 'variableOrder' to the first 'count'-many components of the given 'point'.
   */
std::map<carl::Variable, RAN> toStdMap(
	const RANPoint& point,
	size_t count,
	const std::vector<carl::Variable>& variableOrder) {
	std::map<carl::Variable, RAN> pointAsMap;
	for (size_t i = 0; i < count; i++)
		pointAsMap[variableOrder[i]] = point[i];
	return pointAsMap;
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
std::optional<OpenCADCell> mergeCellWithPoly(
	OpenCADCell& cell,
	const RANPoint& point,
	const std::vector<carl::Variable>& variableOrder,
	const MultiPoly poly) {
	SMTRAT_LOG_INFO("smtrat.opencad", "Merge poly" << poly);
	assert(!carl::is_zero(poly));
	size_t level = levelOf(poly, variableOrder);
	// level for first variable starts at 1, but need it as index to start at 0.
	size_t levelVariableIdx = level - 1;
	SMTRAT_LOG_DEBUG("smtrat.opencad", "At level " << level << " merge it with " << cell);
	if (level == 0) // We have a non-zero, constant-poly, so no roots and nothing to do
		return std::optional<OpenCADCell>(cell);

	auto result = carl::evaluate(
			carl::BasicConstraint<Poly>(poly, carl::Relation::EQ),
			toStdMap(point, level, variableOrder));
	assert(result);
	if (*result) {
		SMTRAT_LOG_WARN("smtrat.opencad", "Poly vanished at point.");
		return std::nullopt;
	}

	std::optional<OpenCADCell> newCell(cell);
	carl::Variable mainVariable = variableOrder[levelVariableIdx];
	SMTRAT_LOG_TRACE("smtrat.opencad", "Current level variable: " << mainVariable);
	MultiCoeffUniPoly polyAsUnivar = carl::to_univariate_polynomial(poly, mainVariable);
	if (level > 1) {
		SMTRAT_LOG_INFO("smtrat.opencad", "Do Open-McCallum projection of this poly into level " << level - 1);
		std::vector<MultiPoly> projectionPolys;
		projectionPolys.emplace_back(polyAsUnivar.lcoeff());
		projectionPolys.emplace_back(MultiPoly(carl::discriminant(polyAsUnivar)));
		SMTRAT_LOG_TRACE("smtrat.opencad", "Add leading coeff: " << polyAsUnivar.lcoeff());
		SMTRAT_LOG_TRACE("smtrat.opencad", "Add discriminant: " << carl::discriminant(polyAsUnivar));

		Sector& sectorAtLvl = (*newCell)[levelVariableIdx];
		// Add resultant of poly and lower sector bound
		if (!sectorAtLvl.isLowBoundNegInfty()) {
			MultiPoly resultant(carl::resultant(carl::to_univariate_polynomial(sectorAtLvl.lowBound->poly, mainVariable), polyAsUnivar));
			projectionPolys.emplace_back(resultant);
			SMTRAT_LOG_TRACE("smtrat.opencad", "Add resultant with cell's low bound: " << resultant);
		}

		// Add resultant of poly and higher sector bound
		if (!sectorAtLvl.isHighBoundInfty()) {
			MultiPoly resultant(carl::resultant(carl::to_univariate_polynomial(sectorAtLvl.highBound->poly,mainVariable), polyAsUnivar));
			projectionPolys.emplace_back(resultant);
			SMTRAT_LOG_TRACE("smtrat.opencad", "Add resultant with cell's high bound: " << resultant);
		}
		SMTRAT_LOG_DEBUG("smtrat.opencad", "Projection result: " << projectionPolys);
		SMTRAT_LOG_INFO("smtrat.opencad", "Projection complete. Merge into cell");

		// Each poly in 'projectionPolys' must be factorized into its irreducible
		// factors.
		carl::CoCoAAdaptor<MultiPoly> factorizer(projectionPolys);
		for (auto& p : projectionPolys) {
			for (const auto& factor : factorizer.irreducibleFactors(p, false)) {
				SMTRAT_LOG_DEBUG("smtrat.opencad", "Merge irreducible factor: " << factor);
				if (!(newCell = mergeCellWithPoly(
						  *newCell,
						  point,
						  variableOrder,
						  factor))) {
					// If submerge fails, this merge fails too
					return std::nullopt;
				}
			}
		}
	}

	// Isolate real roots of level-k 'poly' after plugin in a level-(k-1) point.
	// level is >= 1
	RAN point_k = point[levelVariableIdx]; // called alpha_k in [1]
	SMTRAT_LOG_INFO("smtrat.opencad", "Continue at level " << level
														   << ". Search closest bounds to " << point_k);
	// It must be ensured that poly does not vanish under this point!
	std::vector<RAN> roots = carl::real_roots(polyAsUnivar,
														  toStdMap(point, level - 1, variableOrder)).roots();
	if (roots.empty()) {
		SMTRAT_LOG_INFO("smtrat.opencad", "No bound candidates");
		return newCell;
	}

	std::sort(roots.begin(), roots.end());
	SMTRAT_LOG_DEBUG("smtrat.opencad", "Bound candidates: " << roots);
	Sector& sectorAtLvl = (*newCell)[levelVariableIdx]; // Called D[k] in [1]
	SMTRAT_LOG_DEBUG("smtrat.opencad", "Bounds before: " << sectorAtLvl);

	// Search for closest roots to point_k, i.e.
	// someRoot ... < root_lower < point_k < root_higher < ... someOtherRoot
	auto root_higher = std::find_if(
		roots.begin(),
		roots.end(),
		[&point_k](const RAN& otherPoint) { return otherPoint > point_k; });
	assert(root_higher == roots.end() || *root_higher != point_k);
	// Update high bound if a tighter root is found s.t.
	// point_k < root_higher < cell_highBound
	if (root_higher != roots.end() &&
		(sectorAtLvl.isHighBoundInfty() ||
		 *root_higher < sectorAtLvl.highBound->cachedPoint)) {
		sectorAtLvl.highBound = Section{poly, *root_higher};
	}

	// Update low bound if a tighter root is found s.t.
	// cell_lowBound < root_lower < point_k
	if (root_higher != roots.begin()) {
		auto root_lower = --root_higher;
		assert(*root_lower != point_k);
		if (sectorAtLvl.isLowBoundNegInfty() ||
			*root_lower > sectorAtLvl.lowBound->cachedPoint) {
			sectorAtLvl.lowBound = Section{poly, *root_lower};
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.opencad", "Bounds after: " << sectorAtLvl);
	return newCell;
}

/**
   * Construct a OpenCADCell for the given set of polynomials 'polySet'
   * that contains the given 'point'. The returned cell represents
   * the largest region that is sign-invariant on all polynomials in
   * the 'polySet' and is cylindrical with respect to the
	 * variables ordering given in 'variableOrder'.
	 * Note that this construction is only correct if plugging in
   * the 'point' into any polynomial of the 'polySet' yields a non-zero
   * value, i.e. 'point' is not a root of any polynomial in 'polySet',
	 * otherwise no OpenCADCell is returned.
   * Note that the dimension (number of components) of the 'point' == the number of variables
   * in 'variableOrder'
   * and that  any polynomial of the 'polySet' must be irreducible and
   * mention only variables from 'variableOrder'.
	 *
   */
std::optional<OpenCADCell> createOpenCADCell(
	const std::vector<MultiPoly> polySet,
	const RANPoint& point,
	const std::vector<carl::Variable>& variableOrder) {
	// Note that combining 'variableOrder' and 'point' into
	// a single object like Variable-to-RAN-map
	// is bad because a map may rearrange the variables and destroy
	// any desired variable ordering.
	assert(variableOrder.size() == point.dim());
	SMTRAT_LOG_INFO("smtrat.opencad", "Create BrownOpenOneCell");
	SMTRAT_LOG_DEBUG("smtrat.opencad", "Use point " << point << " wrt. variable order " << variableOrder);

	std::optional<OpenCADCell> cell = createFullspaceCoveringCell(point.dim());
	for (const auto& poly : polySet) {
		SMTRAT_LOG_INFO("smtrat.opencad", "Merge input poly");
		SMTRAT_LOG_DEBUG("smtrat.opencad", "Input poly: " << poly);
		if (!(cell = mergeCellWithPoly(*cell, point, variableOrder, poly))) {
			// If any merge fails, this whole construction fails too
			SMTRAT_LOG_WARN("smtrat.opencad", "Construction failed");
			return std::nullopt;
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.opencad", "Final cell: " << cell.value());
	return cell;
}

} // namespace recursive
} // namespace onecellcad
} // namespace smtrat
