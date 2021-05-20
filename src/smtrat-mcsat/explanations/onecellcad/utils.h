#include <carl/core/polynomialfunctions/Derivative.h>
#include <carl/core/polynomialfunctions/Factorization.h>
#include <carl/core/polynomialfunctions/Resultant.h>

#include <smtrat-cad/projectionoperator/utils.h>
#include <smtrat-common/model.h>
#include <smtrat-common/smtrat-common.h>

#include <algorithm>
#include <optional>
#include <set>
#include <unordered_map>
#include <variant>
#include <vector>

#include <carl/ran/ran.h>
#include <carl/ran/RealAlgebraicPoint.h>
#include <carl/ran/interval/ran_interval_extra.h>


namespace smtrat {
namespace mcsat {
namespace onecellcad {

using RAN = carl::RealAlgebraicNumber<smtrat::Rational>;
using RANMap = std::map<carl::Variable, RAN>;


/**
 * Invariance Types
 */
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

// SIGN_INV < ORD_INV, since order invariance is a "stronger" property.
inline bool operator<(const InvarianceType& l, const InvarianceType& r) {
    switch (l) {
        case InvarianceType::ORD_INV:
            return false;
        case InvarianceType::SIGN_INV:
            return r == InvarianceType ::ORD_INV;
    }
    return false;
}

/**
 * Tagged Polynomials
 */
struct TagPoly {
    InvarianceType tag;

    Poly poly;

    // Cache the poly's level to avoid recomputing it in many places.
    std::size_t level;

    // Optional possibility to cache total degree of polynomial
    std::size_t deg = 0;
};

inline std::ostream& operator<<(std::ostream& os, const TagPoly& p) {
    return os << "(poly " << p.tag << " " << p.poly << ")";
}

inline bool operator==(const TagPoly& lhs, const TagPoly& rhs) {
    return lhs.tag == rhs.tag && lhs.poly == rhs.poly;
}

inline std::ostream& operator<<(std::ostream& os, const std::vector<TagPoly>& polys) {
    os << "[ " << polys.size() << ": ";
    for (const auto& poly : polys)
        os << poly.tag << " " << poly.poly << ", ";
    return os << "]";
}

inline std::ostream& operator<<(std::ostream& os, const std::vector<std::vector<TagPoly>>& lvls) {
    int lvl = (int)lvls.size() - 1;
    for (auto it = lvls.rbegin(); it != lvls.rend(); ++it) {
        os << lvl << ": ";
        os << *it << "\n";
        lvl--;
    }
    return os;
}

/**
* @param p Polynomial to get degree from
* @param v Rootvariable for degree calc
* @return
*/
inline std::size_t getDegree(TagPoly p, carl::Variable v) {
    return carl::total_degree(carl::to_univariate_polynomial(p.poly, v));
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
    //assert(isSubset(asVector(poly.gatherVariables()), variableOrder));

    // Algorithm:
    // Iterate through each variable inside 'variableOrder' in ascending order
    // and remove it from 'polyVariables'. The last variable in 'polyVariables' before
    // it becomes empty is the highest appearing variable in 'poly'.
    //SMTRAT_LOG_DEBUG("smtrat.cad","poly " << poly);

    // 'gatherVariables()' collects only variables with positive degree
    std::set<carl::Variable> polyVariables = carl::variables(poly).as_set();
    //SMTRAT_LOG_DEBUG("smtrat.cad","variables " << polyVariables);

    if(polyVariables.empty()){
        //SMTRAT_LOG_DEBUG("smtrat.cad", "level " << 0);
        return std::nullopt;
    }

    for (std::size_t level = 0; level < variableOrder.size(); ++level) {
        polyVariables.erase(variableOrder[level]);
        // Last variable before 'polyVariables' becomes empty is the highest variable.
        if (polyVariables.empty()) {
            //SMTRAT_LOG_DEBUG("smtrat.cad", "level " << level+1);
            return level;
        }
    }
    throw("Poly contains variable not found in variableOrder");
    return std::nullopt;
}

inline std::vector<TagPoly> nonConstIrreducibleFactors(
        std::vector<carl::Variable> variableOrder,
        Poly poly,
        InvarianceType tag) {

    std::vector<TagPoly> factors;
    for (const Poly& factor : carl::irreducibleFactors(poly, false)) {
        factors.emplace_back(TagPoly{tag, factor, *levelOf(variableOrder, factor)}); // inherit poly's tag
        //SMTRAT_LOG_DEBUG("smtrat.cad", "factor " << factor);
        assert(!factor.isConstant());
    }

    return factors;
}

inline void appendOnCorrectLevel(const Poly& poly, InvarianceType tag, std::vector<std::vector<TagPoly>>& polys, std::vector<carl::Variable> variableOrder) {
    //The invariant of this alg is that we always only have a polynomial with either si or oi in polys
    //This could be violated by the initially entered polys in OneCell construction but that only leads to less efficiency and no error
    std::vector<TagPoly> factors = nonConstIrreducibleFactors(variableOrder, poly, tag);
    // to do carl::normalize()
    for (const auto& factor : factors) {
        if (!factor.poly.isConstant()) {
            TagPoly siFactor = factor;
            TagPoly oiFactor = factor;
            siFactor.tag = InvarianceType::SIGN_INV;
            oiFactor.tag = InvarianceType::ORD_INV;

            auto siContained = std::find(polys[factor.level].begin(), polys[factor.level].end(), siFactor);
            auto oiContained = std::find(polys[factor.level].begin(), polys[factor.level].end(), oiFactor);

            if (siContained == polys[factor.level].end() && oiContained == polys[factor.level].end()) {
                // poly is not yet in vector with either sign-inv. type
                polys[factor.level].push_back(factor);
            } else if (siContained != polys[factor.level].end() && tag == InvarianceType::ORD_INV) {
                polys[factor.level].erase(siContained);
                polys[factor.level].push_back(factor);
            }
        }
    }
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
    return os << "[section " << s.boundFunction << " " << s.isolatedRoot << "]";
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

inline std::ostream& operator<<(std::ostream& os, const Sector& s) {
    os << "(sector ";
    s.lowBound ? os << s.lowBound.value() : os << "[-infty]";
    os << " ";
    s.highBound ? os << s.highBound.value() : os << "[infty]";
    return os << ")";
}


/**
 * Represent a single cell [brown15].
 * A cell is a collection of boundary objects along each axis, called
 * cell-components based on math. vectors and their components.
 */
using CADCell = std::vector<std::variant<Sector, Section>>;

inline std::ostream& operator<<(std::ostream& os, const CADCell& cell) {
    os << "(cell [";
    for (std::size_t i = 0; i < cell.size(); i++) {
        if (std::holds_alternative<Sector>(cell[i])) {
            const auto cellSctr = std::get<Sector>(cell[i]);
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


inline std::vector<Poly> asMultiPolys(const std::vector<TagPoly> polys) {
    std::vector<Poly> mPolys;
    for (const auto& poly : polys)
        mPolys.emplace_back(poly.poly);
    return mPolys;
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
    assert(carl::variables(poly).has(rootVariable));
    // Apparently we need this complicated construction. I forgot why a simple substitute is not okay.
    return MultivariateRootT(Poly(carl::UnivariatePolynomial<Poly>(MultivariateRootT::var(),
                                                                   carl::to_univariate_polynomial(poly, rootVariable).coefficients())),
                             rootIdx);
}

inline carl::RealAlgebraicPoint<smtrat::Rational> asRANPoint(
        const mcsat::Bookkeeping& data) {
    std::vector<carl::RealAlgebraicNumber<smtrat::Rational>> point;
    for (const auto variable : data.assignedVariables()) {
        const auto& modelValue = data.model().evaluated(variable);
        assert(modelValue.isRational() || modelValue.isRAN());
        modelValue.isRational() ? point.emplace_back(modelValue.asRational()) : point.emplace_back(modelValue.asRAN());
    }
    return carl::RealAlgebraicPoint<smtrat::Rational>(std::move(point));
}


template<typename T>
std::vector<T> prefix(const std::vector<T> vars, std::size_t prefixSize) {
    std::vector<T> prefixVars(vars.begin(), std::next(vars.begin(), (long)prefixSize));
    return prefixVars;
}


inline std::vector<std::pair<Poly, Poly>> duplicateElimination(std::vector<std::pair<Poly, Poly>> vec){
    for (auto it1 = vec.begin(); it1 != vec.end();) {
        // also eliminate reflexive pairs since those are already covered by discriminants
        if(it1->first == it1->second){
            it1 = vec.erase(it1);
            continue;
        }
        for (auto it2 = it1 + 1; it2 != vec.end();) {
            if (((*it1).first == (*it2).first && (*it1).second == (*it2).second) ||
                ((*it1).first == (*it2).second && (*it1).second == (*it2).first)) {
                it2 = vec.erase(it2);
            } else {
                it2++;
            }
        }
        it1++;
    }
    return vec;
}

inline std::vector<Poly> duplicateElimination(std::vector<Poly> vec){
    if(!vec.empty()) {
        for (auto it1 = vec.begin(); it1 != vec.end() - 1; it1++) {
            for (auto it2 = it1 + 1; it2 != vec.end();) {
                if (*it1 == *it2) {
                    it2 = vec.erase(it2);
                } else {
                    it2++;
                }
            }
        }
    }
    return vec;
}


/**
 * Projection related utilities for onecellcad
 */

/* Components of Projection operators optimized for Single Cell Construction
        -> For efficiency also return the resulting components level
        -> Also normalize the resulting component w.r.t. the new highest ranked var in the poly
 */
inline Poly discriminant(const carl::Variable& mainVariable, const Poly& p) {
    auto disc = carl::discriminant(carl::to_univariate_polynomial(p, mainVariable));

    return Poly(disc);
}

inline Poly resultant(const carl::Variable& mainVariable, const Poly& p1, const Poly& p2) {
    const auto p1UPoly = carl::to_univariate_polynomial(p1, mainVariable);
    const auto p2UPoly = carl::to_univariate_polynomial(p2, mainVariable);
    auto res = carl::resultant(p1UPoly, p2UPoly);

    return Poly(res);
}
//No normalization for ldcf
inline Poly leadcoefficient(const carl::Variable& mainVariable, const Poly& p) {
    return p.lcoeff(mainVariable);
}


inline void addResultants(std::vector<std::pair<Poly, Poly>> resultants,
        std::vector<std::vector<TagPoly>>& polys,
        carl::Variable mainVar,
        const std::vector<carl::Variable>& variableOrder){
    if(!resultants.empty()) {
        resultants = duplicateElimination(resultants);

        for (auto const& elem : resultants) {
            Poly res = resultant(mainVar, elem.first, elem.second);
            SMTRAT_LOG_TRACE("smtrat.cad", "Add resultant(" << elem.first << "," << elem.second << ") = " << res << " (if not const)");
            appendOnCorrectLevel(res, InvarianceType::ORD_INV, polys, variableOrder);
        }
    }
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

inline CADCell fullSpaceCell(std::size_t cellComponentCount) {
    return CADCell(cellComponentCount);
}

class OneCellCAD {
public:
    /**
     * Variables can also be indexed by level. Polys with mathematical level 1 contain the variable in variableOrder[0]
     */
    const std::vector<carl::Variable>& variableOrder;
    const carl::RealAlgebraicPoint<Rational>& point;


    OneCellCAD(const std::vector<carl::Variable>& variableOrder, const carl::RealAlgebraicPoint<Rational>& point)
            : variableOrder(variableOrder),
              point(point) {
        // precondition:
        assert(!variableOrder.empty());
        assert(hasUniqElems(variableOrder));
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
     * from 'point' (SORTED!).
     */
    std::vector<RAN> isolateLastVariableRoots(
            const std::size_t polyLevel,
            const Poly& poly) {
        // No checks for corectness
        return carl::real_roots(
                carl::to_univariate_polynomial(poly, variableOrder[polyLevel]),
                prefixPointToStdMap(polyLevel)).roots();
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

        return carl::ran::interval::vanishes(
                carl::to_univariate_polynomial(poly, mainVariable),
                prefixPointToStdMap(polyLevel));
    }

    bool isPointRootOfPoly(
            const std::size_t polyLevel,
            const Poly& poly) {
        const std::size_t componentCount = polyLevel + 1;

        //No fail-check here
        auto res = carl::evaluate(
                ConstraintT(poly, carl::Relation::EQ),
                prefixPointToStdMap(componentCount));
        assert(!indeterminate(res));
        return (bool) res;
    }

    inline bool isPointRootOfPoly(
            const TagPoly& poly) {
        return isPointRootOfPoly(poly.level, poly.poly);
    }

    std::optional<Poly> coeffNonNull(const TagPoly& boundCandidate) {
        // This function is similar to "RefNonNull" from [brown15]
        // precondition:
        assert(isNonConstIrreducible(boundCandidate.poly));
        assert(!vanishesEarly(boundCandidate.level, boundCandidate.poly));
        SMTRAT_LOG_TRACE("smtrat.cad", "coeffNonNull");

        const auto mainVariable = variableOrder[boundCandidate.level];
        const auto boundCandidateUniPoly =
                carl::to_univariate_polynomial(boundCandidate.poly, mainVariable);

        // Do early-exit tests:
        for (const auto& coeff : boundCandidateUniPoly.coefficients()) {
            if (coeff.isConstant() && !carl::isZero(coeff))
                return std::nullopt;
        }

        //removed  && contains(polys[*lvl], ldcf) in if
        Poly ldcf = leadcoefficient(mainVariable, boundCandidate.poly);
        std::optional<size_t> lvl = levelOf(variableOrder, ldcf);
        if (lvl.has_value() && !isPointRootOfPoly(*lvl, ldcf)) {
            return std::nullopt;
        }

        //removed  && contains(polys[*lvl], disc) in if
        Poly disc = discriminant(mainVariable, boundCandidate.poly);
        lvl = levelOf(variableOrder, disc);
        if (lvl.has_value() && !isPointRootOfPoly(*lvl, disc)) {
            return std::nullopt;
        }

        // optional early-exit check: if for every point in subcell, poly does not
        // vanish, return success. No idea how to do that efficiently.

        for (const auto& coeff : boundCandidateUniPoly.coefficients()) {
            // find first non-vanishing coefficient:
            if (carl::isZero(coeff)) continue;
            const size_t coeffLevel = *levelOf(variableOrder, coeff); // certainly non-constant
            if (!isPointRootOfPoly(coeffLevel, coeff)) {
                return coeff;
            }
        }
        return std::nullopt;
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
                SMTRAT_LOG_DEBUG("smtrat.cad", "Section: " << cellSctn << " point_" << lvl << ": " << pointCmp);
                if (!(cellSctn.isolatedRoot == pointCmp))
                    return false;
            }
        }
        return true;
    }
};


inline bool optimized_singleLevelFullProjection(
        carl::Variable mainVar,
        size_t currentLevel,
        std::vector<std::vector<TagPoly>>& projectionLevels,
        OneCellCAD& cad) {

    std::vector<TagPoly>& polys = projectionLevels[currentLevel];
    SMTRAT_LOG_DEBUG("smtrat.cad", "Do optimized McCallum projection of " << polys);
    //optimization: Calculate resultants similar to heuristic 2 in a chain (WC-complexity is equal to full projection)
    std::vector<std::pair<RAN, Poly>> root_list;
    for (auto const& tpoly : polys) {
        auto poly = tpoly.poly;

        auto r = carl::real_roots(carl::to_univariate_polynomial(poly, mainVar), cad.prefixPointToStdMap(currentLevel));
        //check for nullification
        if(r.is_nullified()){
            return false;
        }
        for(auto const& root : r.roots()){
            root_list.emplace_back(std::make_pair(root, poly));
        }

        Poly ldcf = leadcoefficient(mainVar, poly);
        SMTRAT_LOG_TRACE("smtrat.cad.projection", "Add leadcoefficient(" << poly << ") = " << ldcf << " (if not const)");
        appendOnCorrectLevel(ldcf, InvarianceType::SIGN_INV, projectionLevels, cad.variableOrder);

        auto coeff = cad.coeffNonNull(tpoly);
        if (coeff.has_value()) {
            SMTRAT_LOG_TRACE("smtrat.cad", "Add result of coeffNonNull: " << coeff.value() << " (if not const)");
            appendOnCorrectLevel(coeff.value(), InvarianceType::SIGN_INV, projectionLevels, cad.variableOrder);
        }

        Poly disc = discriminant(mainVar, poly);
        SMTRAT_LOG_TRACE("smtrat.cad.projection", "Add discriminant(" << poly << ") = " << disc << " (if not const)");
        appendOnCorrectLevel(disc, InvarianceType::ORD_INV, projectionLevels, cad.variableOrder);
    }

    //Resultant calcultaion
    std::sort(root_list.begin(), root_list.end(), [](auto const& t1, auto const& t2) {
        return t1.first < t2.first;
    });

    std::vector<std::pair<Poly, Poly>> resultants;
    if(!root_list.empty()) {
        for (auto it = root_list.begin(); it != root_list.end() - 1; it++) {
            resultants.emplace_back(std::make_pair((*it).second, (*(it+1)).second));
        }
    }
    addResultants(resultants, projectionLevels, mainVar, cad.variableOrder);

    return true;
}

inline void singleLevelFullProjection(
        std::vector<carl::Variable>& variableOrder,
        carl::Variable mainVar,
        size_t currentLevel,
        std::vector<std::vector<TagPoly>>& projectionLevels) {

    std::vector<TagPoly>& polys = projectionLevels[currentLevel];
    SMTRAT_LOG_DEBUG("smtrat.cad", "Do full McCallum projection of " << polys);
    for (std::size_t i = 0; i < polys.size(); i++) {
        Poly poly = polys[i].poly;

        std::vector<Poly> coeffs = carl::to_univariate_polynomial(poly, mainVar).coefficients();
        for (const auto& coeff : coeffs) {
            SMTRAT_LOG_TRACE("smtrat.cad.projection", "Add coefficient(" << poly << ") = " << coeff << " (if not const)");
            appendOnCorrectLevel(coeff, InvarianceType::SIGN_INV, projectionLevels, variableOrder);
        }

        Poly disc = discriminant(mainVar, poly);
        SMTRAT_LOG_TRACE("smtrat.cad.projection", "Add discriminant(" << poly << ") = " << disc << " (if not const)");
        appendOnCorrectLevel(disc, InvarianceType::ORD_INV, projectionLevels, variableOrder);

        std::vector<std::pair<Poly, Poly>> resultants;
        for (std::size_t j = i + 1; j < polys.size(); j++) {
            auto poly2 = polys[j].poly;
            resultants.emplace_back(std::make_pair(poly, poly2));
        }
        addResultants(resultants, projectionLevels, mainVar, variableOrder);
    }
}

} // namespace onecellcad
} // namespace mcsat
} // namespace smtrat