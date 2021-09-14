#pragma once

/**
 * @file
 * Construct a single open CAD Cell IN A LEVEL-WISE MANNER around a given point that is sign-invariant
 * on a given set of polynomials. This is an adaptation of the already existing onecellcad in this project.
 *
 * @author Philippe Specht
 * Contact: philippe.specht@rwth-aachen.de
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
namespace levelwise {

class LevelwiseCAD : public OneCellCAD {
    public:
    using OneCellCAD::OneCellCAD;

    /**
      * Construct a single CADCell that contains the given 'point' and is
      * sign-invariant for the given polynomials in 'polys'.  The construction
      * fails if a polynomial vanishes ( p(a_1,...,a_i-1,x_i) ).  Note that
      * this cell is cylindrical only with respect to the given 'variableOrder'.
      *
      * @param variableOrder must contain unique variables and at least one,
      * because constant polynomials (without a variable) are prohibited.
      * @param point point.size() >= variables.size().
      * @param polys must contain only non-constant, irreducible tagged polynomials that
      * mention only variables that appear in 'variableOrder'.
      *
      */
    std::optional<CADCell> constructCADCellEnclosingPoint(
            std::vector<std::vector<TagPoly>> &polys, int sectionHeuristic, int sectorHeuristic) {
        SMTRAT_LOG_INFO("smtrat.cad", "Build CADcell enclosing point ");
        SMTRAT_LOG_DEBUG("smtrat.cad", "Variable order: " << variableOrder);
        SMTRAT_LOG_DEBUG("smtrat.cad", "Point: " << point);
        for (auto &poly : polys) {
            auto pVec = asMultiPolys(poly);
            SMTRAT_LOG_DEBUG("smtrat.cad", "Polys: " << pVec);
            assert(hasOnlyNonConstIrreducibles(pVec));
            assert(polyVarsAreAllInList(pVec, variableOrder));
        }

        CADCell cell = fullSpaceCell(point.dim());
        SMTRAT_LOG_DEBUG("smtrat.cad", "Cell: " << cell);

        for (int i = (int) point.dim() - 1; i >= 0; i--) {
            carl::Variable rootVariable = variableOrder[i];

            bool sector = true;
            TagPoly t;
            int deg = -1;
            for (auto &poly : polys[i]) {
                if (vanishesEarly(poly.level, poly.poly)) {
                    SMTRAT_LOG_WARN("smtrat.cad",
                                    "Building failed, " << poly.poly << " vanishes early at "
                                                        << point[i]);
                    return std::nullopt;
                } else if (isPointRootOfPoly(poly)) {
                    sector = false;
                    int locDeg = (int) getDegree(poly, rootVariable);
                    assert(locDeg >= 1);
                    // for section: find defining polynomial with smallest degree in i-th variable
                    if (locDeg > deg) {
                        poly.tag = InvarianceType::ORD_INV;
                        t = poly;
                        deg = locDeg;
                    }
                }
            }

            const RAN pointComp = point[i];
            if (!sector) {
                /** Current level is a Section */
                SMTRAT_LOG_DEBUG("smtrat.cad", "Shrink cell sector at lvl " << i + 1);
                SMTRAT_LOG_TRACE("smtrat.cad", "Transform to section");
                SMTRAT_LOG_TRACE("smtrat.cad", "Defining poly: " << t.poly);
                SMTRAT_LOG_TRACE("smtrat.cad", "Lvl-Var: " << variableOrder[i]);
                SMTRAT_LOG_DEBUG("smtrat.cad", "PointComp: " << pointComp);

                assert(isNonConstIrreducible(t.poly));
                assert(t.level == (size_t) i);

                auto isolatedRoots = isolateLastVariableRoots(t.level, t.poly);
                assert(!isolatedRoots.empty());
                SMTRAT_LOG_TRACE("smtrat.cad", "Isolated roots: " << isolatedRoots);

                std::size_t rootIdx = 0;
                bool found = false;
                for (const auto &root : isolatedRoots) {
                    rootIdx++;
                    if (root == pointComp) {
                        SMTRAT_LOG_TRACE("smtrat.cad", "Equal: " << root);
                        cell[i] = Section{asRootExpr(rootVariable, t.poly, rootIdx), root};
                        SMTRAT_LOG_TRACE("smtrat.cad", "Resulting section: "
                                << (Section{asRootExpr(rootVariable, t.poly, rootIdx), root}));
                        found = true;
                        break;
                    }
                }
                assert(found);

                /** Projection part for section case*/
                if (i != 0) {
                    //Project polynomial that defines section
                    SMTRAT_LOG_TRACE("smtrat.cad", "Begin projection in section case");

                    Poly disc = discriminant(variableOrder[i], t.poly);
                    SMTRAT_LOG_TRACE("smtrat.cad", "Add discriminant: " << disc << " (if not const)");
                    appendOnCorrectLevel(disc, InvarianceType::ORD_INV, polys, variableOrder);


                    Poly ldcf = leadcoefficient(variableOrder[i], t.poly);
                    SMTRAT_LOG_TRACE("smtrat.cad",
                                     "Add leadcoefficient: " << ldcf << " (if not const)");
                    appendOnCorrectLevel(ldcf, InvarianceType::SIGN_INV, polys, variableOrder);


                    std::vector<std::tuple<RAN, TagPoly>> upper;
                    std::vector<std::tuple<RAN, TagPoly>> lower;
                    std::vector<std::pair<Poly, Poly>> resultants;
                    std::vector<Poly> noDisc1;
                    std::vector<Poly> noDisc2;
                    std::vector<Poly> noLdcf;
                    //project rest of polynomials


                    if (sectionHeuristic == 1) {
                        for (auto &poly : polys[i]) {
                            //Heuristic 1: calculate resultant between defining pol t and every pol that has root above or below t
                            if (!isolateLastVariableRoots(poly.level, poly.poly).empty()) {
                                if (poly.poly != t.poly) {
                                    resultants.emplace_back(std::make_pair(t.poly, poly.poly));
                                }
                            }
                        }

                    } else if (sectionHeuristic == 2) {
                        for (auto &poly : polys[i]) {
                            //Heuristic 2: calculate resultant in chain-form over lower and upper
                            SMTRAT_LOG_TRACE("smtrat.cad", "Poly: " << poly.poly);
                            std::vector<RAN> isolatedRoots = isolateLastVariableRoots(poly.level,
                                                                                      poly.poly);

                            if (isolatedRoots.empty()) {
                                SMTRAT_LOG_TRACE("smtrat.cad", "No isolatable isolatedRoots");
                                continue;
                            } else {
                                SMTRAT_LOG_TRACE("smtrat.cad", "Isolated roots: " << isolatedRoots);
                            }

                            //guaranteed at least one root
                            //find closest root above and below sample (if existent) and put into upper and lower respectively
                            if (isolatedRoots.front() >= pointComp) {
                                //poly only has roots above pointComp
                                SMTRAT_LOG_DEBUG("smtrat.cad", "Smallest root above PointComp(1): "
                                        << isolatedRoots.front());
                                upper.emplace_back(std::make_tuple(isolatedRoots.front(), poly));
                            } else if (isolatedRoots.back() <= pointComp) {
                                //poly only has roots below pointComp
                                SMTRAT_LOG_DEBUG("smtrat.cad", "Biggest root below PointComp(1): "
                                        << isolatedRoots.back());
                                lower.emplace_back(std::make_tuple(isolatedRoots.back(), poly));
                            } else {
                                auto lb = std::lower_bound(isolatedRoots.begin(), isolatedRoots.end(),
                                                           pointComp);
                                if (*(lb - 1) == std::get<Section>(cell[i]).isolatedRoot) {
                                    SMTRAT_LOG_DEBUG("smtrat.cad", "Root at PointComp: " << *(lb - 1));
                                    lower.emplace_back(std::make_tuple(*(lb - 1), poly));
                                } else {
                                    //poly has root above and below pointComp
                                    SMTRAT_LOG_DEBUG("smtrat.cad",
                                                     "Smallest root above PointComp(2): " << *lb);
                                    upper.emplace_back(std::make_tuple(*lb, poly));
                                    SMTRAT_LOG_DEBUG("smtrat.cad",
                                                     "Biggest root below PointComp(2): " << *(lb - 1));
                                    lower.emplace_back(std::make_tuple(*(lb - 1), poly));
                                }
                            }

                            //Additionally calculate disc
                            disc = discriminant(variableOrder[i], poly.poly);
                            SMTRAT_LOG_TRACE("smtrat.cad",
                                             "Add discriminant: " << disc << " (if not const)");
                            appendOnCorrectLevel(disc, InvarianceType::ORD_INV, polys, variableOrder);
                        }

                        //sort closest roots of pols below and above sample
                        std::sort(lower.begin(), lower.end(), [](auto const &t1, auto const &t2) {
                            return std::get<0>(t1) < std::get<0>(t2);
                        });
                        std::sort(upper.begin(), upper.end(), [](auto const &t1, auto const &t2) {
                            return std::get<0>(t1) < std::get<0>(t2);
                        });

                        //calculate resultants
                        if (!lower.empty()) {
                            for (auto it = lower.begin(); it != lower.end() - 1; it++) {
                                resultants.emplace_back(std::make_pair(std::get<1>(*it).poly,
                                                                       std::get<1>(*(it + 1)).poly));
                            }
                        }

                        if (!lower.empty() && !upper.empty()) {
                            resultants.emplace_back(std::make_pair(std::get<1>(lower.back()).poly,
                                                                   std::get<1>(upper.front()).poly));
                        }

                        if (!upper.empty()) {
                            for (auto it = upper.begin(); it != upper.end() - 1; it++) {
                                resultants.emplace_back(std::make_pair(std::get<1>(*it).poly,
                                                                       std::get<1>(*(it + 1)).poly));
                            }
                        }

                        // Need no ldcf if its beginning or end of resultant-chain and has poly above and below sample
                        if (!lower.empty() && std::find_if(upper.begin(), upper.end(),
                                                           [&](auto const &t1) {
                                                               return (std::get<1>(t1).poly == std::get<1>(*lower.begin()).poly);
                                                           }) != upper.end()) {
                            noLdcf.emplace_back(std::get<1>(*lower.begin()).poly);
                        }
                        if (!upper.empty() && std::find_if(lower.begin(), lower.end(),
                                                           [&](auto const &t1) {
                                                               return (std::get<1>(t1).poly == std::get<1>(*(upper.end() - 1)).poly);
                                                           }) != lower.end()) {
                            noLdcf.emplace_back(std::get<1>(*(upper.end() - 1)).poly);
                        }

                        for (auto &poly : polys[i]) {
                            if (!contains(noLdcf, poly.poly)) {
                                ldcf = leadcoefficient(variableOrder[i], poly.poly);
                                SMTRAT_LOG_TRACE("smtrat.cad", "Add leadcoefficient: " << ldcf << " (if not const)");
                                appendOnCorrectLevel(ldcf, InvarianceType::SIGN_INV, polys, variableOrder);
                            }
                        }

                    } else if (sectionHeuristic == 3) {
                        for (auto &poly : polys[i]) {
                            //Heuristic 3: smart
                            SMTRAT_LOG_TRACE("smtrat.cad", "Poly: " << poly.poly);
                            std::vector<RAN> isolatedRoots = isolateLastVariableRoots(poly.level, poly.poly);

                            if (isolatedRoots.empty()) {
                                SMTRAT_LOG_TRACE("smtrat.cad", "No isolatable isolatedRoots");
                                continue;
                            } else {
                                SMTRAT_LOG_TRACE("smtrat.cad", "Isolated roots: " << isolatedRoots);
                            }

                            //guaranteed at least one root
                            //find closest root above and below sample (if existent) and put into upper and lower respectively
                            poly.deg = getDegree(poly, rootVariable);
                            if (isolatedRoots.front() >= pointComp) {
                                //poly only has roots above pointComp
                                SMTRAT_LOG_DEBUG("smtrat.cad", "Smallest root above PointComp(1): "
                                        << isolatedRoots.front());
                                upper.emplace_back(std::make_tuple(isolatedRoots.front(), poly));
                            } else if (isolatedRoots.back() <= pointComp) {
                                //poly only has roots below pointComp
                                SMTRAT_LOG_DEBUG("smtrat.cad", "Biggest root below PointComp(1): "
                                        << isolatedRoots.back());
                                lower.emplace_back(std::make_tuple(isolatedRoots.back(), poly));
                            } else {
                                auto lb = std::lower_bound(isolatedRoots.begin(), isolatedRoots.end(), pointComp);
                                if (*(lb - 1) == std::get<Section>(cell[i]).isolatedRoot) {
                                    SMTRAT_LOG_DEBUG("smtrat.cad", "Root at PointComp: " << *(lb - 1));
                                    lower.emplace_back(std::make_tuple(*(lb - 1), poly));
                                } else {
                                    //poly has root above and below pointComp
                                    SMTRAT_LOG_DEBUG("smtrat.cad",
                                                     "Smallest root above PointComp(2): " << *lb);
                                    upper.emplace_back(std::make_tuple(*lb, poly));
                                    SMTRAT_LOG_DEBUG("smtrat.cad",
                                                     "Biggest root below PointComp(2): " << *(lb - 1));
                                    lower.emplace_back(std::make_tuple(*(lb - 1), poly));
                                }
                            }
                        }

                        //sort closest roots of pols below and above sample
                        std::sort(lower.begin(), lower.end(), [](auto const &t1, auto const &t2) {
                            return std::get<0>(t1) < std::get<0>(t2);
                        });
                        std::sort(upper.begin(), upper.end(), [](auto const &t1, auto const &t2) {
                            return std::get<0>(t1) < std::get<0>(t2);
                        });

                        //calculate resultants
                        if (!lower.empty()) {
                            //optimization: for multiple entries with the same root in lower, sort the one with the
                            //  lowest degree to the smallest possible position for optimal resultant calculation
                            for (auto it = lower.begin() + 1; it != lower.end(); it++) {
                                if (std::get<0>(*(it - 1)) == std::get<0>(*it) &&
                                    std::get<1>(*(it - 1)).deg < std::get<1>(*it).deg) {
                                    std::iter_swap(it - 1, it);
                                }
                            }

                            auto mark = lower.rend()-1;
                            while (mark != lower.rbegin()) {
                                auto cur = std::min_element(lower.rbegin(), mark, [](auto const &t1, auto const &t2) {
                                    return std::get<1>(t1).deg < std::get<1>(t2).deg;
                                });

                                for (auto it = cur + 1; it != mark+1; it++) {
                                    resultants.emplace_back(std::make_pair(std::get<1>(*cur).poly, std::get<1>(*it).poly));
                                    // Ldcfs of pols not necessary if they  are only connected to 1 pol AND also appear on the other side of sample point
                                    if (std::find_if(upper.begin(), upper.end(),
                                                     [&](auto const &t1) { return (std::get<1>(t1).poly == std::get<1>(*it).poly); }) != upper.end()) {
                                        noLdcf.emplace_back(std::get<1>(*it).poly);
                                    }
                                }

                                mark = cur;

                                #ifdef SMTRAT_DEVOPTION_Statistics
                                    getStatistic().resultantBarrierCreated();
                                #endif
                            }

                            // optimization: find polynomials only connected to bound t because they need no discriminant
                            if (!resultants.empty()) {
                                resultants = duplicateElimination(resultants);
                                for (auto &res : resultants) {
                                    if (res.first == t.poly) {
                                        noDisc1.push_back(res.second);
                                    }
                                    if (res.second == t.poly) {
                                        noDisc1.push_back(res.first);
                                    }
                                }
                                if (!noDisc1.empty()) {
                                    duplicateElimination(noDisc1);
                                    bool inc;
                                    for (auto it = noDisc1.begin(); it != noDisc1.end();) {
                                        inc = true;
                                        for (auto &res : resultants) {
                                            if ((res.first == *it && res.second != t.poly) ||
                                                (res.second == *it && res.first != t.poly)) {
                                                it = noDisc1.erase(it);
                                                inc = false;
                                                break;
                                            }
                                        }
                                        if (inc) { it++; }
                                    }
                                }
                            }
                        }

                        std::vector<std::pair<Poly, Poly>> tmpResultants;
                        if (!upper.empty()) {
                            //optimization: for multiple entries with the same root in upper, sort the one with the
                            //  lowest degree to the smallest possible position for optimal resultant calculation
                            for (auto it = upper.begin() + 1; it != upper.end(); it++) {
                                if (std::get<0>(*(it - 1)) == std::get<0>(*it) &&
                                    std::get<1>(*(it - 1)).deg > std::get<1>(*it).deg) {
                                    std::iter_swap(it - 1, it);
                                }
                            }

                            auto mark = upper.end()-1;
                            while (mark != upper.begin()) {
                                auto cur = std::min_element(upper.begin(), mark, [](auto const &t1, auto const &t2) {
                                    return std::get<1>(t1).deg < std::get<1>(t2).deg;
                                });

                                for (auto it = cur + 1; it != mark+1; it++) {
                                    tmpResultants.emplace_back(std::make_pair(std::get<1>(*cur).poly, std::get<1>(*it).poly));
                                    // Ldcfs of pols not necessary if they  are only connected to 1 pol AND also appear on the other side of  sample point
                                    if (std::find_if(lower.begin(), lower.end(),
                                                     [&](auto const &t1) { return (std::get<1>(t1).poly == std::get<1>(*it).poly); }) != lower.end()) {
                                        noLdcf.emplace_back(std::get<1>(*it).poly);
                                    }
                                }

                                mark = cur;

                                #ifdef SMTRAT_DEVOPTION_Statistics
                                    getStatistic().resultantBarrierCreated();
                                #endif
                            }

                            // optimization: find polynomials only connected to bound t because they need no discriminant
                            if (!tmpResultants.empty()) {
                                tmpResultants = duplicateElimination(tmpResultants);
                                for (auto &res : tmpResultants) {
                                    if (res.first == t.poly) {
                                        noDisc2.push_back(res.second);
                                    }
                                    if (res.second == t.poly) {
                                        noDisc2.push_back(res.first);
                                    }
                                }
                                if (!noDisc2.empty()) {
                                    duplicateElimination(noDisc2);
                                    bool inc;
                                    for (auto it = noDisc2.begin(); it != noDisc2.end();) {
                                        inc = true;
                                        for (auto &res : tmpResultants) {
                                            if ((res.first == *it && res.second != t.poly) ||
                                                (res.second == *it && res.first != t.poly)) {
                                                it = noDisc2.erase(it);
                                                inc = false;
                                                break;
                                            }
                                        }
                                        if (inc) { it++; }
                                    }
                                }
                                resultants.insert(resultants.end(), tmpResultants.begin(), tmpResultants.end());
                                tmpResultants.clear();
                            }
                        }

                        if (!lower.empty() && !upper.empty()) {
                            resultants.emplace_back(std::make_pair(std::get<1>(lower.back()).poly,
                                                                   std::get<1>(upper.front()).poly));
                        }

                        //Additionally calculate discs and ldcfs (if necessary)
                        for (auto &poly : polys[i]) {
                            if (!contains(noDisc1, poly.poly) && !contains(noDisc2, poly.poly)) {
                                disc = discriminant(variableOrder[i], poly.poly);
                                SMTRAT_LOG_TRACE("smtrat.cad", "Add discriminant: " << disc << " (if not const)");
                                appendOnCorrectLevel(disc, InvarianceType::ORD_INV, polys, variableOrder);
                            }

                            if (!contains(noLdcf, poly.poly)) {
                                ldcf = leadcoefficient(variableOrder[i], poly.poly);
                                SMTRAT_LOG_TRACE("smtrat.cad", "Add leadcoefficient: " << ldcf << " (if not const)");
                                appendOnCorrectLevel(ldcf, InvarianceType::SIGN_INV, polys, variableOrder);
                            }
                        }

                    } else {
                        SMTRAT_LOG_WARN("smtrat.cad", "Building failed: Incorrect heuristic input");
                        return std::nullopt;
                    }

                    for (auto &poly : polys[i]) {
                        if (poly.poly != t.poly) {
                            if (isPointRootOfPoly(poly)) {
                                if (poly.tag == InvarianceType::ORD_INV) {
                                    SMTRAT_LOG_TRACE("smtrat.cad", "Check for vanishing coefficient");
                                    auto coeff = coeffNonNull(poly);
                                    if (coeff.has_value()) {
                                        SMTRAT_LOG_TRACE("smtrat.cad", "Add result of coeffNonNull: " << coeff.value() << " (if not const)");
                                        appendOnCorrectLevel(coeff.value(), InvarianceType::SIGN_INV, polys, variableOrder);
                                    }
                                    if (sectionHeuristic == 1) {
                                        //for other heuristics, discriminants have already been calculated
                                        disc = discriminant(variableOrder[i], poly.poly);
                                        SMTRAT_LOG_TRACE("smtrat.cad", "Add discriminant: " << disc << " (if not const)");
                                        appendOnCorrectLevel(disc, InvarianceType::ORD_INV, polys, variableOrder);
                                    }
                                }
                            } else {
                                poly.tag = InvarianceType::ORD_INV;
                            }
                        }
                    }

                    // Add all calculate resultants (independent from heuristic)
                    addResultants(resultants, polys, variableOrder[i], variableOrder);
                }
            } else {
                /** Current level is a Sector */
                Sector &sector = std::get<Sector>(cell[i]);
                SMTRAT_LOG_DEBUG("smtrat.cad", "Shrink cell sector at lvl " << i + 1);
                SMTRAT_LOG_DEBUG("smtrat.cad", "Lvl-var: " << variableOrder[i]);
                SMTRAT_LOG_DEBUG("smtrat.cad", "PointComp: " << pointComp);
                SMTRAT_LOG_DEBUG("smtrat.cad", "Determine sector, currently: " << sector);

                std::vector<TagPoly> upper1;
                std::vector<TagPoly> lower1;
                std::vector<std::tuple<RAN, TagPoly, int>> upper2;
                std::vector<std::tuple<RAN, TagPoly, int>> lower2;
                std::vector<Poly> noLdcf;
                TagPoly curUp;
                TagPoly curLow;
                // Different heuristics for resultant calculation need different setups of control data
                // Level 1 does not need control data at all
                if (i == 0) {
                    for (const auto &poly : polys[i]) {
                        SMTRAT_LOG_TRACE("smtrat.cad", "Poly: " << poly.poly);

                        auto isolatedRoots = isolateLastVariableRoots(poly.level, poly.poly);

                        if (isolatedRoots.empty()) {
                            SMTRAT_LOG_TRACE("smtrat.cad", "No isolatable isolatedRoots");
                            continue;
                        } else {
                            SMTRAT_LOG_TRACE("smtrat.cad", "Isolated roots: " << isolatedRoots);
                        }

                        // Search for closest isolatedRoots/boundPoints to pointComp, i.e.
                        // someRoot ... < closestLower < pointComp < closestUpper < ... someOtherRoot
                        std::optional<RAN> closestLower, closestUpper;
                        int rootIdx = 0, lowerRootIdx = 0, upperRootIdx = 0;

                        for (const auto &root : isolatedRoots) {
                            rootIdx++;
                            if (root < pointComp) {
                                SMTRAT_LOG_TRACE("smtrat.cad", "Smaller: " << root);
                                if (!closestLower || *closestLower < root) {
                                    closestLower = root;
                                    lowerRootIdx = rootIdx;
                                    curLow = poly;
                                }
                            } else { // pointComp < root
                                SMTRAT_LOG_TRACE("smtrat.cad", "Bigger: " << root);
                                if (!closestUpper || root < *closestUpper) {
                                    closestUpper = root;
                                    upperRootIdx = rootIdx;
                                    curUp = poly;
                                }
                                //break out of loop since isolatedRoots is sorted
                                break;
                            }
                        }

                        if (closestLower) {
                            if (!sector.lowBound || (*(sector.lowBound)).isolatedRoot < closestLower) {
                                sector.lowBound = Section{
                                        asRootExpr(rootVariable, poly.poly, lowerRootIdx),
                                        *closestLower};
                                SMTRAT_LOG_TRACE("smtrat.cad", "New lower bound: "
                                        << " " << sector);
                            }
                        }

                        if (closestUpper) {
                            if (!sector.highBound ||
                                closestUpper < (*(sector.highBound)).isolatedRoot) {
                                sector.highBound = Section{
                                        asRootExpr(rootVariable, poly.poly, upperRootIdx),
                                        *closestUpper};
                                SMTRAT_LOG_TRACE("smtrat.cad", "New upper bound: "
                                        << " " << sector);
                            }
                        }
                    }

                } else if (sectorHeuristic == 1) {
                    // for convenience, upper2 (lower2 respectively) is used here to save all possible upper bounds
                    // => poly with smallest degree in i-th variable is then chosen
                    std::optional<RAN> closestLower, closestUpper;
                    for (const auto &poly : polys[i]) {
                        SMTRAT_LOG_TRACE("smtrat.cad", "Poly: " << poly.poly);

                        auto isolatedRoots = isolateLastVariableRoots(poly.level, poly.poly);

                        if (isolatedRoots.empty()) {
                            SMTRAT_LOG_TRACE("smtrat.cad", "No isolatable isolatedRoots");
                            continue;
                        } else {
                            SMTRAT_LOG_TRACE("smtrat.cad", "Isolated roots: " << isolatedRoots);
                        }

                        // Search for closest isolatedRoots/boundPoints to pointComp, i.e.
                        // someRoot ... < closestLower < pointComp < closestUpper < ... someOtherRoot
                        bool up = false, low = false;
                        int rootIdx = 0;
                        for (const auto &root : isolatedRoots) {
                            rootIdx++;
                            if (root < pointComp) {
                                SMTRAT_LOG_TRACE("smtrat.cad", "Smaller: " << root);
                                low = true;
                                if (!closestLower || *closestLower < root) {
                                    closestLower = root;
                                    lower2.clear();
                                    lower2.emplace_back(std::make_tuple(root, poly, rootIdx));
                                } else if (*closestLower == root) {
                                    lower2.emplace_back(std::make_tuple(root, poly, rootIdx));
                                }
                            } else { // pointComp < root
                                SMTRAT_LOG_TRACE("smtrat.cad", "Bigger: " << root);
                                up = true;
                                if (!closestUpper || root < *closestUpper) {
                                    closestUpper = root;
                                    upper2.clear();
                                    upper2.emplace_back(std::make_tuple(root, poly, rootIdx));
                                } else if (*closestUpper == root) {
                                    upper2.emplace_back(std::make_tuple(root, poly, rootIdx));
                                } else {
                                    // Optimization: break out of loop since isolatedRoots is sorted
                                    break;
                                }
                            }
                        }

                        if (low) {
                            lower1.push_back(poly);
                        }

                        if (up) {
                            upper1.push_back(poly);
                        }
                    }

                    // Set bounds according to degree that is first calculated
                    if (!lower2.empty()) {
                        for (auto elem : lower2) {
                            std::get<1>(elem).deg = getDegree(std::get<1>(elem), rootVariable);
                        }
                        auto smallest = *std::min_element(lower2.begin(), lower2.end(),
                                                          [](auto const &t1, auto const &t2) {
                                                              return std::get<1>(t1).deg < std::get<1>(t2).deg;
                                                          });

                        curLow = std::get<1>(smallest);
                        sector.lowBound = Section{
                                asRootExpr(rootVariable, curLow.poly, std::get<2>(smallest)),
                                std::get<0>(smallest)};
                        SMTRAT_LOG_TRACE("smtrat.cad", "New lower bound: "
                                << " " << sector);
                    }

                    if (!upper2.empty()) {
                        for (auto elem : upper2) {
                            std::get<1>(elem).deg = getDegree(std::get<1>(elem), rootVariable);
                        }
                        auto smallest = *std::min_element(upper2.begin(), upper2.end(),
                                                          [](auto const &t1, auto const &t2) {
                                                              return std::get<1>(t1).deg < std::get<1>(t2).deg;
                                                          });

                        curUp = std::get<1>(smallest);
                        sector.highBound = Section{
                                asRootExpr(rootVariable, curUp.poly, std::get<2>(smallest)),
                                std::get<0>(smallest)};
                        SMTRAT_LOG_TRACE("smtrat.cad", "New upper bound: "
                                << " " << sector);
                    }

                    // polys with root above and below sample need no ldcf
                    for (auto &poly : polys[i]) {
                        if (contains(lower1, poly) && contains(upper1, poly)) {
                            noLdcf.emplace_back(poly.poly);
                        }
                    }

                } else if (sectorHeuristic == 2) {
                    //while determining bounds create lists upper2 and lower2 which are sorted by their order around the sample
                    for (const auto &poly : polys[i]) {
                        SMTRAT_LOG_TRACE("smtrat.cad", "Poly: " << poly.poly);
                        std::vector<RAN> isolatedRoots = isolateLastVariableRoots(poly.level,
                                                                                  poly.poly);

                        if (isolatedRoots.empty()) {
                            SMTRAT_LOG_TRACE("smtrat.cad", "No isolatable isolatedRoots");
                            continue;
                        } else {
                            SMTRAT_LOG_TRACE("smtrat.cad", "Isolated roots: " << isolatedRoots);
                        }

                        //guaranteed at least one root
                        //find closest root above and below sample (if existent) and put into upper2 and lower2 respectively
                        if (isolatedRoots.front() > pointComp) {
                            //poly only has roots above pointComp
                            SMTRAT_LOG_DEBUG("smtrat.cad", "Smallest root above PointComp(1): "
                                    << isolatedRoots.front());
                            upper2.emplace_back(std::make_tuple(isolatedRoots.front(), poly, 1));
                        } else if (isolatedRoots.back() < pointComp) {
                            //poly only has roots below pointComp
                            SMTRAT_LOG_DEBUG("smtrat.cad", "Biggest root below PointComp(1): "
                                    << isolatedRoots.back());
                            lower2.emplace_back(std::make_tuple(isolatedRoots.back(), poly,
                                                                isolatedRoots.end() -
                                                                isolatedRoots.begin()));
                        } else {
                            auto lb = std::lower_bound(isolatedRoots.begin(), isolatedRoots.end(),
                                                       pointComp);
                            //poly has root above and below pointComp
                            SMTRAT_LOG_DEBUG("smtrat.cad", "Smallest root above PointComp(2): " << *lb);
                            upper2.emplace_back(
                                    std::make_tuple(*lb, poly, (int) (lb - isolatedRoots.begin()) + 1));
                            SMTRAT_LOG_DEBUG("smtrat.cad",
                                             "Biggest root below PointComp(2): " << *(lb - 1));
                            lower2.emplace_back(std::make_tuple(*(lb - 1), poly,
                                                                (int) (lb - isolatedRoots.begin())));
                        }
                    }

                    //sort closest roots of pols below and above sample
                    std::sort(lower2.begin(), lower2.end(), [](auto const &t1, auto const &t2) {
                        return std::get<0>(t1) < std::get<0>(t2);
                    });
                    std::sort(upper2.begin(), upper2.end(), [](auto const &t1, auto const &t2) {
                        return std::get<0>(t1) < std::get<0>(t2);
                    });

                    if (!lower2.empty()) {
                        // find lower bound with smallest degree in i-th variable
                        auto curPos = lower2.rbegin();
                        int curDeg = -1;
                        auto it = lower2.rbegin() + 1;
                        while (it != lower2.rend()) {
                            if (std::get<0>(*it) == std::get<0>(*curPos)) {
                                if (curDeg == -1) {
                                    curDeg = (int) getDegree(std::get<1>(*curPos), rootVariable);
                                }
                                int degree = (int) getDegree(std::get<1>(*it), rootVariable);
                                if (degree < curDeg) {
                                    curPos = it;
                                    curDeg = degree;
                                }
                                it++;
                            } else {
                                break;
                            }
                        }
                        std::iter_swap(curPos.base() - 1, lower2.end() - 1);


                        //set lower bound
                        curLow = std::get<1>(lower2.back());
                        sector.lowBound = Section{
                                asRootExpr(rootVariable, curLow.poly, std::get<2>(lower2.back())),
                                std::get<0>(lower2.back())};
                        SMTRAT_LOG_TRACE("smtrat.cad", "Lower bound: "
                                << " " << *sector.lowBound);

                    } else {
                        SMTRAT_LOG_TRACE("smtrat.cad", "Open lower bound");
                    }

                    if (!upper2.empty()) {
                        // find upper bound with smallest degree in i-th variable
                        auto curPos = upper2.begin();
                        int curDeg = -1;
                        auto it = upper2.begin() + 1;
                        while (it != upper2.end()) {
                            if (std::get<0>(*it) == std::get<0>(*curPos)) {
                                if (curDeg == -1) {
                                    curDeg = (int) getDegree(std::get<1>(*curPos), rootVariable);
                                }
                                int degree = (int) getDegree(std::get<1>(*it), rootVariable);
                                if (degree < curDeg) {
                                    curPos = it;
                                    curDeg = degree;
                                }
                                it++;
                            } else {
                                break;
                            }
                        }
                        std::iter_swap(curPos, upper2.begin());

                        //set upper bound
                        curUp = std::get<1>(upper2.front());
                        sector.highBound = Section{
                                asRootExpr(rootVariable, curUp.poly, std::get<2>(upper2.front())),
                                std::get<0>(upper2.front())};
                        SMTRAT_LOG_TRACE("smtrat.cad", "Upper bound: "
                                << " " << *sector.highBound);
                    } else {
                        SMTRAT_LOG_TRACE("smtrat.cad", "Open upper bound");
                    }

                } else if (sectorHeuristic == 3) {
                    //while determining bounds create lists upper2 and lower2 which are sorted by their order around the sample
                    for (auto &poly : polys[i]) {
                        SMTRAT_LOG_TRACE("smtrat.cad", "Poly: " << poly.poly);
                        std::vector<RAN> isolatedRoots = isolateLastVariableRoots(poly.level,
                                                                                  poly.poly);

                        if (isolatedRoots.empty()) {
                            SMTRAT_LOG_TRACE("smtrat.cad", "No isolatable isolatedRoots");
                            continue;
                        } else {
                            SMTRAT_LOG_TRACE("smtrat.cad", "Isolated roots: " << isolatedRoots);
                        }

                        //guaranteed at least one root
                        //find closest root above and below sample (if existent) and put into upper2 and lower2 respectively
                        poly.deg = getDegree(poly, rootVariable);
                        if (isolatedRoots.front() > pointComp) {
                            //poly only has roots above pointComp
                            SMTRAT_LOG_DEBUG("smtrat.cad", "Smallest root above PointComp(1): "
                                    << isolatedRoots.front());
                            upper2.emplace_back(std::make_tuple(isolatedRoots.front(), poly, 1));
                        } else if (isolatedRoots.back() < pointComp) {
                            //poly only has roots below pointComp
                            SMTRAT_LOG_DEBUG("smtrat.cad", "Biggest root below PointComp(1): "
                                    << isolatedRoots.back());
                            lower2.emplace_back(std::make_tuple(isolatedRoots.back(), poly, (int) (isolatedRoots.end() - isolatedRoots.begin())));
                        } else {
                            auto lb = std::lower_bound(isolatedRoots.begin(), isolatedRoots.end(), pointComp);
                            //poly has root above and below pointComp
                            SMTRAT_LOG_DEBUG("smtrat.cad", "Smallest root above PointComp(2): " << *lb);
                            upper2.emplace_back(std::make_tuple(*lb, poly, (int) (lb - isolatedRoots.begin()) + 1));
                            SMTRAT_LOG_DEBUG("smtrat.cad",
                                             "Biggest root below PointComp(2): " << *(lb - 1));
                            lower2.emplace_back(std::make_tuple(*(lb - 1), poly, (int) (lb - isolatedRoots.begin())));
                        }
                    }
                    //sort closest roots of pols below and above sample
                    std::sort(lower2.begin(), lower2.end(), [](auto const &t1, auto const &t2) {
                        return std::get<0>(t1) < std::get<0>(t2);
                    });
                    std::sort(upper2.begin(), upper2.end(), [](auto const &t1, auto const &t2) {
                        return std::get<0>(t1) < std::get<0>(t2);
                    });

                    if (!lower2.empty()) {
                        //optimization: for multiple entries with the same root in lower2, sort the one with the
                        //  lowest degree to the biggest possible position for optimal resultant calculation
                        for (auto it = lower2.begin() + 1; it != lower2.end(); it++) {
                            if (std::get<0>(*(it - 1)) == std::get<0>(*it) &&
                                std::get<1>(*(it - 1)).deg > std::get<1>(*it).deg) {
                                std::iter_swap(it - 1, it);
                            }
                        }

                        //set lower bound
                        curLow = std::get<1>(lower2.back());
                        sector.lowBound = Section{
                                asRootExpr(rootVariable, curLow.poly, std::get<2>(lower2.back())),
                                std::get<0>(lower2.back())};
                        SMTRAT_LOG_TRACE("smtrat.cad", "Lower bound: " << " " << sector);

                    } else {
                        SMTRAT_LOG_TRACE("smtrat.cad", "Open lower bound");
                    }

                    if (!upper2.empty()) {
                        //optimization: for multiple entries with the same root in upper2, sort the one with the
                        //  lowest degree to the smallest possible position for optimal resultant calculation
                        for (auto it = upper2.begin() + 1; it != upper2.end(); it++) {
                            if (std::get<0>(*(it - 1)) == std::get<0>(*it) &&
                                std::get<1>(*(it - 1)).deg > std::get<1>(*it).deg) {
                                std::iter_swap(it - 1, it);
                            }
                        }

                        //set upper bound
                        curUp = std::get<1>(upper2.front());
                        sector.highBound = Section{
                                asRootExpr(rootVariable, curUp.poly, std::get<2>(upper2.front())),
                                std::get<0>(upper2.front())};
                        SMTRAT_LOG_TRACE("smtrat.cad", "Upper bound: "
                                << " " << sector);

                    } else {
                        SMTRAT_LOG_TRACE("smtrat.cad", "Open upper bound");
                    }
                } else {
                    SMTRAT_LOG_WARN("smtrat.cad", "Building failed: Incorrect heuristic input");
                    return std::nullopt;
                }
                SMTRAT_LOG_TRACE("smtrat.cad", "Determined bounds of sector: " << sector);


                /** Projection part for sector case*/
                if (i != 0) {
                    SMTRAT_LOG_TRACE("smtrat.cad", "Begin projection in sector case");
                    for (auto &poly : polys[i]) {
                        //Add discriminant
                        Poly disc = discriminant(variableOrder[i], poly.poly);
                        SMTRAT_LOG_TRACE("smtrat.cad",
                                         "Add discriminant(" << poly.poly << ") = " << disc << " (if not const)");
                        appendOnCorrectLevel(disc, InvarianceType::ORD_INV, polys, variableOrder);

                        SMTRAT_LOG_TRACE("smtrat.cad", "Check for vanishing coefficient");
                        auto coeff = coeffNonNull(poly);
                        if (coeff.has_value()) {
                            SMTRAT_LOG_TRACE("smtrat.cad",
                                             "Add result of coeffNonNull: " << coeff.value() << " (if not const)");
                            appendOnCorrectLevel(coeff.value(), InvarianceType::SIGN_INV, polys, variableOrder);
                        }

                        poly.tag = InvarianceType::ORD_INV;
                    }

                    //Calculate and comulatively append resultants and leadcoefficients
                    std::vector<std::pair<Poly, Poly>> resultants;

                    if (sector.lowBound.has_value() && sector.highBound.has_value() &&
                        sector.lowBound->boundFunction.poly() !=
                        sector.highBound->boundFunction.poly()) {

                        resultants.emplace_back(std::make_pair(curLow.poly, curUp.poly));
                    }

                    if (sectorHeuristic == 1) {
                        //Heuristic 1: calculate resultant between upper/lower bound and every polynomial above/below
                        if (sector.lowBound.has_value()) {
                            for (const auto &l : lower1) {
                                if (l.poly != curLow.poly) {
                                    resultants.emplace_back(std::make_pair(l.poly, curLow.poly));
                                }
                            }
                        }

                        if (sector.highBound.has_value()) {
                            for (const auto &u : upper1) {
                                if (u.poly != curUp.poly) {
                                    resultants.emplace_back(std::make_pair(u.poly, curUp.poly));
                                }
                            }
                        }

                        // Need no ldcf if it also appears on other side
                        for (auto &element : lower2) {
                            if (std::find_if(upper2.begin(), upper2.end(),
                                             [&](auto const &t1) { return (std::get<1>(t1).poly == std::get<1>(element).poly); }) !=
                                upper2.end()) {
                                noLdcf.emplace_back(std::get<1>(element).poly);
                            }
                        }

                         for (auto &element : upper2) {
                            if (std::find_if(lower2.begin(), lower2.end(),
                                             [&](auto const &t1) { return (std::get<1>(t1).poly == std::get<1>(element).poly); }) !=
                                lower2.end()) {
                                noLdcf.emplace_back(std::get<1>(element).poly);
                            }
                        }

                    } else if (sectorHeuristic == 2) {
                        //Heuristic 2: calculate resultant in chain-form over lower2 and upper2
                        if (sector.lowBound.has_value()) {
                            for (auto it = lower2.begin(); it != lower2.end() - 1; it++) {
                                resultants.emplace_back(std::make_pair(std::get<1>(*it).poly,
                                                                       std::get<1>(*(it + 1)).poly));
                            }
                        }

                        if (sector.highBound.has_value()) {
                            for (auto it = upper2.begin(); it != upper2.end() - 1; it++) {
                                resultants.emplace_back(std::make_pair(std::get<1>(*it).poly,
                                                                       std::get<1>(*(it + 1)).poly));
                            }
                        }

                        // Need no ldcf if its beginning or end of resultant-chain and has poly above and below sample
                        if (!lower2.empty() && std::find_if(upper2.begin(), upper2.end(), [&](auto const &t1) {
                            return (std::get<1>(t1).poly == std::get<1>(*lower2.begin()).poly);
                        }) != upper2.end()) {
                            noLdcf.emplace_back(std::get<1>(*lower2.begin()).poly);
                        }
                        if (!upper2.empty() && std::find_if(lower2.begin(), lower2.end(), [&](auto const &t1) {
                            return (std::get<1>(t1).poly == std::get<1>(*(upper2.end() - 1)).poly);
                        }) != lower2.end()) {
                            noLdcf.emplace_back(std::get<1>(*(upper2.end() - 1)).poly);
                        }

                    } else if (sectorHeuristic == 3) {
                        //heuristic 3: smart
                        if (!lower2.empty()) {
                            //optimization: for multiple entries with the same root in lower, sort the one with the
                            //  lowest degree to the smallest possible position for optimal resultant calculation
                            for (auto it = lower2.begin() + 1; it != lower2.end(); it++) {
                                if (std::get<0>(*(it - 1)) == std::get<0>(*it) &&
                                    std::get<1>(*(it - 1)).deg < std::get<1>(*it).deg) {
                                    std::iter_swap(it - 1, it);
                                }
                            }

                            auto mark = lower2.rend()-1;
                            while (mark != lower2.rbegin()) {
                                auto cur = std::min_element(lower2.rbegin(), mark,
                                                            [](auto const &t1, auto const &t2) {
                                                                return std::get<1>(t1).deg < std::get<1>(t2).deg;
                                                            });

                                for (auto it = cur + 1; it != mark+1; it++) {
                                    resultants.emplace_back(std::get<1>(*cur).poly, std::get<1>(*it).poly);
                                    // Ldcfs of pols not necessary if they  are only connected to 1 pol AND also appear on the other side of  sample point
                                    if (std::find_if(upper2.begin(), upper2.end(),
                                                     [&](auto const &t1) { return (std::get<1>(t1).poly == std::get<1>(*it).poly); }) !=
                                        upper2.end()) {
                                        noLdcf.emplace_back(std::get<1>(*it).poly);
                                    }
                                }

                                mark = cur;
                                #ifdef SMTRAT_DEVOPTION_Statistics
                                    getStatistic().resultantBarrierCreated();
                                #endif
                            }
                        }

                        if (!upper2.empty()) {
                            //optimization: for multiple entries with the same root in upper, sort the one with the
                            //  lowest degree to the smallest possible position for optimal resultant calculation
                            for (auto it = upper2.begin() + 1; it != upper2.end(); it++) {
                                if (std::get<0>(*(it - 1)) == std::get<0>(*it) &&
                                    std::get<1>(*(it - 1)).deg > std::get<1>(*it).deg) {
                                    std::iter_swap(it - 1, it);
                                }
                            }

                            auto mark = upper2.end()-1;
                            while (mark != upper2.begin()) {
                                auto cur = std::min_element(upper2.begin(), mark,
                                                            [](auto const &t1, auto const &t2) {
                                                                return std::get<1>(t1).deg <
                                                                       std::get<1>(t2).deg;
                                                            });

                                for (auto it = cur + 1; it != mark+1; it++) {
                                    resultants.emplace_back(std::get<1>(*cur).poly, std::get<1>(*it).poly);
                                    // Ldcfs of pols not necessary if they  are only connected to 1 pol AND also appear on the other side of  sample point
                                    if (std::find_if(lower2.begin(), lower2.end(),
                                                     [&](auto const &t1) { return (std::get<1>(t1).poly == std::get<1>(*it).poly); }) !=
                                        lower2.end()) {
                                        noLdcf.emplace_back(std::get<1>(*it).poly);
                                    }
                                }

                                mark = cur;
                                #ifdef SMTRAT_DEVOPTION_Statistics
                                    getStatistic().resultantBarrierCreated();
                                #endif
                            }
                        }

                    } else {
                        SMTRAT_LOG_WARN("smtrat.cad", "Building failed: Incorrect heuristic input");
                        return std::nullopt;
                    }

                    lower1.clear();
                    upper1.clear();
                    lower2.clear();
                    upper2.clear();

                    //Add resultants and leadcoefficients depending on heuristic
                    addResultants(resultants, polys, variableOrder[i], variableOrder);

                    for (auto &poly : polys[i]) {
                        if (!contains(noLdcf, poly.poly)) {
                            Poly ldcf = leadcoefficient(variableOrder[i], poly.poly);
                            SMTRAT_LOG_TRACE("smtrat.cad", "Add leadcoefficient(" << poly.poly << ") = " << ldcf << " (if not const)");
                            appendOnCorrectLevel(ldcf, InvarianceType::SIGN_INV, polys, variableOrder);
                        }
                    }

                    /** optimize memory*/
                    resultants.clear();
                } else {
                    SMTRAT_LOG_TRACE("smtrat.cad", "Level 1, so no projection");
                }
            }
            /** optimize memory*/
            polys[i].clear();
        }

        SMTRAT_LOG_DEBUG("smtrat.cad", "Finished Cell: " << cell);
        assert(isMainPointInsideCell(cell));
        return cell;
    }
};


} // namespace levelwise
} // namespace onecellcad
} // namespace mcsat
} // namespace smtrat