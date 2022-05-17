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

#include "../Assertables.h"
#include "../utils.h"


namespace smtrat {
namespace mcsat {
namespace onecellcad {
namespace recursive {



bool cover_nullification;

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

class RecursiveCAD : public OneCellCAD {
private:
	/**
     * Projection factor set divided into levels. Polys with mathematical level 1 are at projFactorSet[0]
     * This collection is called "P_prj" in [brown15]
     */
	std::vector<std::vector<TagPoly>> projFactorSet; // init all levels with empty vector

	/** Only delinating polys. This collection is called "P_dln" in [brown15] */
	std::vector<TagPoly> delineators;

public:
    using OneCellCAD::OneCellCAD;

    bool isAlreadyProcessed(const TagPoly& poly) {
		// matches if poly is found with its tag or an oi-tag
		auto isMatch = [&poly](const TagPoly& processedPoly) {
			return processedPoly.poly == poly.poly &&
				   (processedPoly.tag == poly.tag || processedPoly.tag == InvarianceType::ORD_INV);
		};
		auto& log = projFactorSet[poly.level];
		if (std::find_if(log.begin(), log.end(), isMatch) != log.end())
			return true;

		return std::find_if(delineators.begin(), delineators.end(), isMatch) != delineators.end();
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

		std::size_t rootIdx = 0, lowerRootIdx = 0, upperRootIdx = 0;
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
	std::vector<Poly> partialDerivativesLayerWithSomeNonEarlyVanishingPoly(const TagPoly& mainPoly) {
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
					if (carl::is_zero(derivative))
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

	ShrinkResult refineNull(
		const TagPoly& boundCandidate,
		CADCell& cell) {
		// This function is called "RefNull" in [brown15]
		// precondition:
		assert(isNonConstIrreducible(boundCandidate.poly));
		assert(isPointRootOfPoly(boundCandidate));
		SMTRAT_LOG_TRACE("smtrat.cad", "RefineNull");
		const auto mainVariable = variableOrder[boundCandidate.level];
		const auto boundCandidateUniPoly =
			carl::to_univariate_polynomial(boundCandidate.poly, mainVariable);
		std::vector<TagPoly> projectionResult;

		Poly disc = discriminant(mainVariable, boundCandidate.poly);
		if(!disc.isConstant()){
            projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, disc, *levelOf(variableOrder, disc)});

        }

		auto ldcf = leadcoefficient(mainVariable, boundCandidate.poly);
        if(!disc.isConstant()) {
            projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, ldcf, *levelOf(variableOrder, ldcf)});
        }

		Poly tcf = boundCandidateUniPoly.tcoeff();
        std::optional<size_t> lvl = levelOf(variableOrder, tcf);
        if(lvl.has_value()) {
            projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, tcf, *lvl});
        }

		for (auto& resultPoly : projectionResult) {
			if (shrinkCellWithIrreducibleFactorsOfPoly(resultPoly, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;
		}

		return ShrinkResult::SUCCESS;
	}

	ShrinkResult shrinkCellWithEarlyVanishingPoly(
		const TagPoly& boundCandidate,
		CADCell& cell) {
		// This function is called MergeNull in [brown15]
		// precondition:
        SMTRAT_LOG_TRACE("smtrat.cad", "ShrinkWithEarlyVanishingPoly");
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
				 partialDerivativesLayerWithSomeNonEarlyVanishingPoly(boundCandidate)) {
				if (!vanishesEarly(boundCandidate.level, boundCandidate.poly))
					delineator += poly * poly;
			}

			if (!delineator.isConstant()) {
				const std::size_t delineatorLevel = *levelOf(variableOrder, delineator);
				shrinkSingleComponent(delineatorLevel, delineator, cell);

				const TagPoly taggedDelineator{
					InvarianceType::ORD_INV,
					delineator,
					delineatorLevel};
				projFactorSet[delineatorLevel].emplace_back(taggedDelineator);
				delineators.emplace_back(taggedDelineator);
			}
			return ShrinkResult::SUCCESS;
		}
	}

	ShrinkResult shrinkCellWithIrreducibleFactorsOfPoly(
		const TagPoly& poly,
		CADCell& cell) {
		for (const auto& factor : carl::irreducibleFactors(poly.poly, false)) {
			SMTRAT_LOG_TRACE("smtrat.cad", "Shrink with irreducible factor: Poly: "
											   << poly.poly << " Factor: " << factor);
			if (factor.isConstant())
				continue;

			const std::size_t factorLevel = *levelOf(variableOrder, factor);
			TagPoly factorWithInheritedTag{poly.tag, factor, factorLevel};
			if (shrinkCell(factorWithInheritedTag, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;
		}
		return ShrinkResult::SUCCESS;
	}

	ShrinkResult refineNonNull(
		const TagPoly& boundCandidate,
		CADCell& cell) {
		// This function is called "RefNonNull" in [brown15]
		// precondition:
		assert(isNonConstIrreducible(boundCandidate.poly));
		assert(!vanishesEarly(boundCandidate.level, boundCandidate.poly));
		SMTRAT_LOG_TRACE("smtrat.cad", "RefineNonNull");

		const auto mainVariable = variableOrder[boundCandidate.level];
		const auto boundCandidateUniPoly =
			carl::to_univariate_polynomial(boundCandidate.poly, mainVariable);

		// Do early-exit tests:
		for (const auto& coeff : boundCandidateUniPoly.coefficients()) {
			if (coeff.isConstant() && !carl::is_zero(coeff))
				return ShrinkResult::SUCCESS;
		}

		const Poly ldcf = leadcoefficient(mainVariable, boundCandidate.poly);
		std::optional<size_t> lvl = levelOf(variableOrder, ldcf);
		if (lvl.has_value() && (contains(projFactorSet[*lvl], ldcf) || contains(delineators, ldcf)) && !isPointRootOfPoly(*lvl, ldcf)) {
			return ShrinkResult::SUCCESS;
		}

		const Poly disc = discriminant(mainVariable, boundCandidate.poly);
        lvl = levelOf(variableOrder, disc);
        if (lvl.has_value() && (contains(projFactorSet[*lvl], disc) || contains(delineators, disc)) && !isPointRootOfPoly(*lvl, disc)) {
			return ShrinkResult::SUCCESS;
		}

		// optional early-exit check: if for every point in subcell, poly does not
		// vanish, return success. No idea how to do that efficiently.

		for (const auto& coeff : boundCandidateUniPoly.coefficients()) {
			// find first non-vanishing coefficient:
			if (carl::is_zero(coeff)) continue;
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
		const TagPoly& boundCandidate,
		CADCell& cell) {
		// This function is called MergeRoot in [brown15]
		// precondition:
		assert(!vanishesEarly(boundCandidate.level, boundCandidate.poly));
		assert(isPointRootOfPoly(boundCandidate));
		SMTRAT_LOG_TRACE("smtrat.cad", "ShrinkWithPolyHavingPointAsRoot");

		// Do a "model-based" Brown-McCallum projection.
		std::vector<TagPoly> projectionResult;
		const auto mainVariable = variableOrder[boundCandidate.level];
		if (std::holds_alternative<Section>(cell[boundCandidate.level])) {
		    Poly res = resultant(mainVariable, boundCandidate.poly,
		            std::get<Section>(cell[boundCandidate.level]).boundFunction.poly(mainVariable));
            if(!res.isConstant()){
                projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, res, *levelOf(variableOrder, res)});
            }

			if (boundCandidate.tag == InvarianceType::ORD_INV) {
			    Poly ldcf = leadcoefficient(mainVariable, boundCandidate.poly);
                if(!ldcf.isConstant()) {
                    projectionResult.emplace_back(TagPoly{InvarianceType::SIGN_INV, ldcf, *levelOf(variableOrder, ldcf)});
                }

                Poly disc = discriminant(mainVariable, boundCandidate.poly);
                if(!disc.isConstant()) {
                    projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, disc, *levelOf(variableOrder, disc)});
                }
			}
		} else { // cellComponent is a Sector at 'boundCandidate's level
            Poly ldcf = leadcoefficient(mainVariable, boundCandidate.poly);
            if(!ldcf.isConstant()) {
                projectionResult.emplace_back(TagPoly{InvarianceType::SIGN_INV, ldcf, *levelOf(variableOrder, ldcf)});
            }

            Poly disc = discriminant(mainVariable, boundCandidate.poly);
            if(!disc.isConstant()) {
                projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, disc, *levelOf(variableOrder, disc)});
            }

			Sector& sectorAtLvl = std::get<Sector>(cell[boundCandidate.level]);

			if (sectorAtLvl.lowBound) {
			    Poly res = resultant(mainVariable, boundCandidate.poly, sectorAtLvl.lowBound->boundFunction.poly(mainVariable));
                if(!res.isConstant()) {
                    projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, res, *levelOf(variableOrder, res)});
                }
			}
			if (sectorAtLvl.highBound) {
                Poly res = resultant(mainVariable, boundCandidate.poly, sectorAtLvl.highBound->boundFunction.poly(mainVariable));
                if(!res.isConstant()) {
                    projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, res, *levelOf(variableOrder, res)});
                }
			}
		}

		for (auto& resultPoly : projectionResult) {
			if (shrinkCellWithIrreducibleFactorsOfPoly(resultPoly, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;
		}

		if (boundCandidate.tag == InvarianceType::ORD_INV ||
			std::holds_alternative<Sector>(cell[boundCandidate.level])) {
			if (refineNonNull(boundCandidate, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;

			shrinkSingleComponent(boundCandidate.level, boundCandidate.poly, cell);
		}

		projFactorSet[boundCandidate.level].emplace_back(TagPoly{
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
		const TagPoly& boundCandidate,
		CADCell& cell) {
		// This function is called "MergeNotRoot" in [brown15]
		// precondition:
		assert(isNonConstIrreducible(boundCandidate.poly));
		assert(!isPointRootOfPoly(boundCandidate));
		SMTRAT_LOG_TRACE("smtrat.cad", "ShrinkWithNonRootPoint");

		// Do a "model-based" Brown-McCallum projection.
		std::vector<TagPoly> projectionResult;
		const auto mainVariable = variableOrder[boundCandidate.level];
		if (std::holds_alternative<Section>(cell[boundCandidate.level])) {
			Section sectionAtLvl = std::get<Section>(cell[boundCandidate.level]);
            Poly res = resultant(mainVariable, boundCandidate.poly, sectionAtLvl.boundFunction.poly(mainVariable));
            if(!res.isConstant()) {
                projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, res, *levelOf(variableOrder, res)});
            }
		} else {	 // cellComponent is a Sector at 'boundCandidate's level
            Poly disc = discriminant(mainVariable, boundCandidate.poly);
            if(!disc.isConstant()) {
                projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, disc, *levelOf(variableOrder, disc)});
            }

			Sector sectorAtLvl = std::get<Sector>(cell[boundCandidate.level]);
			if (!sectorAtLvl.lowBound || !sectorAtLvl.highBound ||
				hasPolyLastVariableRootWithinBounds(
					sectorAtLvl.lowBound->isolatedRoot,
					sectorAtLvl.highBound->isolatedRoot,
					boundCandidate.poly,
					boundCandidate.level)) {
                Poly ldcf = leadcoefficient(mainVariable, boundCandidate.poly);
                if(!ldcf.isConstant()) {
                    projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, ldcf, *levelOf(variableOrder, ldcf)});
                }
			}

			if (sectorAtLvl.lowBound) {
                Poly res = resultant(mainVariable, boundCandidate.poly, sectorAtLvl.lowBound->boundFunction.poly(mainVariable));
                if(!res.isConstant()) {
                    projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, res, *levelOf(variableOrder, res)});
                }
			}
			if (sectorAtLvl.highBound) {
                Poly res = resultant(mainVariable, boundCandidate.poly, sectorAtLvl.highBound->boundFunction.poly(mainVariable));
                if(!res.isConstant()) {
                    projectionResult.emplace_back(TagPoly{InvarianceType::ORD_INV, res, *levelOf(variableOrder, res)});
                }
			}
		}

		for (auto resultPoly : projectionResult) {
			if (shrinkCellWithIrreducibleFactorsOfPoly(resultPoly, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;
		}

		if (std::holds_alternative<Sector>(cell[boundCandidate.level])) {
			if (refineNonNull(boundCandidate, cell) == ShrinkResult::FAIL)
				return ShrinkResult::FAIL;

			shrinkSingleComponent(boundCandidate.level, boundCandidate.poly, cell);
		}

		projFactorSet[boundCandidate.level].emplace_back(TagPoly{
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
		const TagPoly& boundCandidate,
		CADCell& cell) {
		// This function is called "Merge" in [brown15]
		SMTRAT_LOG_INFO("smtrat.cad", "Shrink cell");
		SMTRAT_LOG_DEBUG("smtrat.cad", "Poly: " << boundCandidate);
		SMTRAT_LOG_DEBUG("smtrat.cad", "Cell: " << cell);
        // precondition:
        //if(!isPointInsideCell(cell)){
        //    std::exit(77);
        //}
        assert(isMainPointInsideCell(cell));

		if (isAlreadyProcessed(boundCandidate))
			return ShrinkResult::SUCCESS;

		if (cellDimension(cell, boundCandidate.level) == 0) {
			projFactorSet[boundCandidate.level].emplace_back(TagPoly{InvarianceType::ORD_INV, boundCandidate.poly, boundCandidate.level});
			return ShrinkResult::SUCCESS;
		}

		if (boundCandidate.level == 0) {
			if (std::holds_alternative<Sector>(cell[boundCandidate.level]))
				shrinkSingleComponent(boundCandidate.level, boundCandidate.poly, cell);
			projFactorSet[boundCandidate.level].emplace_back(TagPoly{InvarianceType::ORD_INV, boundCandidate.poly, boundCandidate.level});
			return ShrinkResult::SUCCESS;
		}

		if (vanishesEarly(boundCandidate.level, boundCandidate.poly)) {
			if (cover_nullification) {
				return shrinkCellWithEarlyVanishingPoly(boundCandidate, cell);
			} else {
				return ShrinkResult::FAIL;
			}
		}

		// lower level subcell
		if (cellDimension(cell, boundCandidate.level - 1) == 0) {
			shrinkSingleComponent(boundCandidate.level, boundCandidate.poly, cell);
			projFactorSet[boundCandidate.level].emplace_back(TagPoly{InvarianceType::ORD_INV, boundCandidate.poly, boundCandidate.level});
			return ShrinkResult::SUCCESS;
		}

		if (isPointRootOfPoly(boundCandidate))
			return shrinkCellWithPolyHavingPointAsRoot(boundCandidate, cell);
		else
			return shrinkCellWithNonRootPoint(boundCandidate, cell);
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
		const std::vector<std::vector<onecellcad::TagPoly>>& polys) {

		SMTRAT_LOG_INFO("smtrat.cad", "Build point enclosing CADcell");
		SMTRAT_LOG_DEBUG("smtrat.cad", "Variable order: " << variableOrder);
		SMTRAT_LOG_DEBUG("smtrat.cad", "Point: " << point);
        auto it = polys.rbegin();
        while(it != polys.rend()) {
            auto pVec = asMultiPolys(*it);
            SMTRAT_LOG_DEBUG("smtrat.cad", "Polys: " << pVec);
            assert(hasOnlyNonConstIrreducibles(pVec));
            assert(polyVarsAreAllInList(pVec, variableOrder));
            it++;
        }

        projFactorSet.resize(point.dim());
		CADCell cell = fullSpaceCell(point.dim());
		SMTRAT_LOG_DEBUG("smtrat.cad", "Cell: " << cell);

		for (const auto& polyVec : polys) {
            for (const auto& poly : polyVec) {
                if (shrinkCell(poly, cell) == ShrinkResult::FAIL) {
                    SMTRAT_LOG_WARN("smtrat.cad", "Building failed");
                    return std::nullopt;
                }
            }
		}

		SMTRAT_LOG_DEBUG("smtrat.cad", "Finished Cell: " << cell);
		assert(isMainPointInsideCell(cell));
		return cell;
	}
};

} // namespace recursive
} // namespace onecellcad
} // namespace mcsat
} // namespace smtrat
