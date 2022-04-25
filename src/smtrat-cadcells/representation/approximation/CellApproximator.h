#include "ran_approximation.h"
#include "criteria.h"

namespace smtrat::cadcells::representation::approximation {

using IR = datastructures::IndexedRoot;

enum ApxPoly {
    SIMPLE,
    LINEAR_GRADIENT,
    LINEAR_GRADIENT_MULTI,
    UNIVARIATE_TAYLOR,
    MULTIVARIATE_TAYLOR,
    HYPERPLANE
};

struct ApxSettings {
    static constexpr ApxPoly bound = ApxPoly::SIMPLE;
    static constexpr ApxPoly between = ApxPoly::SIMPLE;
    static constexpr std::size_t taylor_deg = 2;
    static constexpr std::size_t hyperplane_dim = 0;
    static constexpr ApxRoot root = ApxRoot::SAMPLE_MID;
    static constexpr std::size_t n_sb_iterations = 1;
    static constexpr double root_ratio = 0.5;
};

class CellApproximator {
    private:
        datastructures::Projections& m_r_proj;
        const datastructures::DelineationInterval& m_r_del;
        carl::Variable m_var;
        Assignment m_sample;

        datastructures::Projections& proj() {return m_r_proj;}
        const datastructures::DelineationInterval& del() const {return m_r_del;}
        carl::Variable var() const {return m_var;}
        Assignment sample() const {return m_sample;}
        RAN main_sample() {return m_sample[m_var];}

        template<ApxPoly PA>
        IR apx_bound(const IR& p, const RAN& bound, bool below);

        template<ApxPoly PA>
        IR apx_between(const IR& p_l, const IR& p_u, const RAN& l, const RAN& u);
    public:
        template<typename T>
        CellApproximator(datastructures::SampledDerivationRef<T>& der) 
        : m_r_proj(der->proj()), m_r_del(der->cell()), m_var(der->main_var()),
          m_sample(der->sample()) {}

        IR approximate_bound(const IR& p, const RAN& bound, bool below);
        IR approximate_between(const IR& p_l, const IR& p_u, const RAN& l, const RAN& u);

        datastructures::CellDescription compute_cell();
};

template<>
IR CellApproximator::apx_bound<ApxPoly::SIMPLE>(const IR& p, const RAN& bound, bool below) {
    return IR(proj().polys()(Poly(var()) - approximate_root<ApxSettings::root>(main_sample(),bound,below)), 1);
}

template<>
IR CellApproximator::apx_bound<ApxPoly::LINEAR_GRADIENT>(const IR& p, const RAN& bound, bool below) {
    Poly derivative = carl::derivative(proj().polys()(p.poly), var());
    auto apx_point = sample();
    apx_point[var()] = bound;
    auto gradient = carl::evaluate(derivative, apx_point);
    assert(gradient);
    Rational approximate_gradient = approximate_RAN(*gradient);
    if (approximate_gradient == Rational(0)) return apx_bound<ApxPoly::SIMPLE>(p, bound, below);
    return IR(proj().polys()(approximate_gradient*Poly(var()) - approximate_gradient*Poly(approximate_root<ApxSettings::root>(main_sample(),bound,below))), 1);
}

template<>
IR CellApproximator::apx_bound<ApxPoly::LINEAR_GRADIENT_MULTI>(const IR& p, const RAN& bound, bool below) {
    Poly derivative = carl::derivative(proj().polys()(p.poly), var());
    Poly gradient = carl::substitute(derivative, var(), Poly(approximate_RAN(bound)));
    if (gradient.isZero()) return apx_bound<ApxPoly::SIMPLE>(p, bound, below);
    return IR(proj().polys()(gradient*Poly(var()) - gradient*approximate_root<ApxSettings::root>(main_sample(),bound,below)), 1);
}

template<>
IR CellApproximator::apx_bound<ApxPoly::UNIVARIATE_TAYLOR>(const IR& p, const RAN& bound, bool below) {
    assert(ApxSettings::taylor_deg < proj().degree(p.poly));
    Poly result;
    Poly powers(1);
    Poly deriv = proj().polys()(p.poly);
    RAN deriv_evaluated;
    auto sample_root = sample();
    sample_root[var()] = bound;
    Rational apx_point = approximate_root<ApxSettings::root>(main_sample(), bound, below);
    for (std::size_t i = 1; i <= ApxSettings::taylor_deg; i++) {
        deriv = Poly(Rational(1)/Rational(i)) * carl::derivative(deriv, var());
        deriv_evaluated = *carl::evaluate(deriv, sample());
        powers = powers * (Poly(var()) - Poly(apx_point));
        result = result + Poly(approximate_RAN(deriv_evaluated))*powers; // TODO: better apx than branching_point
    }

    return IR(proj().polys()(result), 1); // TODO : which index?
}

template<>
IR CellApproximator::apx_bound<ApxPoly::MULTIVARIATE_TAYLOR>(const IR& p, const RAN& bound, bool below) {
    assert(ApxSettings::taylor_deg < proj().degree(p.poly));
    assert(ApxSettings::taylor_deg <= 2);
    std::size_t dim = sample().size();
    VariableOrdering var_order = proj().polys().var_order();
    auto sample_root = sample();
    sample_root[var()] = bound; // TODO : can choose other points here (like the actual sample)
    auto sample_new_root = sample();
    sample_new_root[var()] = RAN(approximate_root<ApxSettings::root>(main_sample(), bound, below));

    #ifdef SMTRAT_DEVOPTION_Statistics
        std::size_t leftOutVars = 0;
        for (const auto& [var, val] : sample_new_root) {
            if (!val.is_numeric()) ++leftOutVars;
        }
        OCApproximationStatistics::get_instance().leftOutVarsTaylor(leftOutVars);
    #endif

    auto one_step_differentiate = [&var_order, &sample_root, &sample_new_root, this, dim] (const Poly& poly, Poly& result, std::vector<Poly>& jacobian) {
        Rational evaluated_deriv;
        for (std::size_t i = 0; i < dim; i++) {
            // Skip variables with irrational assignment, since (x_i - s_i) cannot be used
            if (!sample_new_root[var_order[i]].is_numeric()) continue;
            jacobian[i] = carl::derivative(poly, var_order[i]);
            evaluated_deriv = approximate_RAN(*carl::evaluate(jacobian[i], sample_root));
            result = result + Poly(evaluated_deriv) * (Poly(var_order[i]) - Poly(approximate_RAN(sample_new_root[var_order[i]])));
        }
        // return the sign of the main variable derivative
        if (carl::isZero(evaluated_deriv)) return 0;
        else if (evaluated_deriv > 0) return 1;
        else return -1;
    };

    std::vector<Poly> jacobian(dim);
    Poly result;
    // first order taylor approximation
    int jacobian_sign = one_step_differentiate(proj().polys()(p.poly), result, jacobian);
    if ((ApxSettings::taylor_deg < 2) && (jacobian_sign == 0)) {
        return apx_bound<ApxPoly::SIMPLE>(p, bound, below);
    }
    // second order
    if (ApxSettings::taylor_deg == 2) {
        int hessian_sign = 0;
        for (std::size_t i = 0; i < dim; i++) {
            if (!sample_new_root[var_order[i]].is_numeric()) continue;
            std::vector<Poly> hessian_row(dim);
            Poly res_i;
            hessian_sign = one_step_differentiate(jacobian[i], res_i, hessian_row);
            result = result + (Poly(Rational(1)/Rational(2)) * (Poly(var_order[i]) - Poly(approximate_RAN(sample_new_root[var_order[i]]))) * res_i); 
        }
        auto restricted_sample = sample();
        restricted_sample.erase(var());
        auto roots = carl::real_roots(carl::to_univariate_polynomial(result, var()), restricted_sample);
        
        if (hessian_sign == 0 && jacobian_sign == 0) return apx_bound<ApxPoly::SIMPLE>(p, bound, below);
        else if (hessian_sign*jacobian_sign == 1) {
            assert(roots.is_univariate());
            assert(roots.roots()[1] == sample_new_root[var()]);
            if (below) assert(roots.roots()[1] > bound && roots.roots()[1] < main_sample());
            else assert(roots.roots()[1] < bound && roots.roots()[1] > main_sample());
            return IR(proj().polys()(result), 2);
        }
        assert(roots.is_univariate());
        assert(roots.roots()[0] == sample_new_root[var()]);
        if (below) assert(roots.roots()[0] > bound && roots.roots()[0] < main_sample());
        else assert(roots.roots()[0] < bound && roots.roots()[0] > main_sample());
    }
    return IR(proj().polys()(result), 1);
}

/*template<>
IR CellApproximator::apx_bound<ApxPoly::HYPERPLANE>(const IR& p, const RAN& bound, bool below) {
    std::size_t dimensions =sample().size()-1;
    if (ApxSettings::hyperplane_dim != 0) dimensions = std::min(ApxSettings::hyperplane_dim, dimensions);
    if (dimensions == 0) return apx_bound<ApxPoly::SIMPLE>(p, bound, below);
    datastructures::PolyRef discriminant = proj.disc(p.poly);
    datastructures::PolyRef leading_coeff = proj.ldcf(p.poly);
    carl::UnivariatePolynomial<Poly> poly = carl::to_univariate_polynomial(proj.polys()(p.poly), var());
    VariableOrdering var_order = proj.polys().var_order();
    Poly result = Poly(var()) - Poly(approximate_root<ApxSettings::root>(main_sample(), bound, below));
    for (std::size_t i = 1; i <= dimensions; i++) {
        carl::Variable v = var_order[sample.size()-i -1];
        auto restricted_sample =sample();
        restricted_sample.erase(v);
        Rational sample_below = carl::floor(sample()[v]);
        Rational sample_above = carl::ceil(sample()[v]);
        if (sample_below == sample_above) {
            sample_below = sample_below - (Rational(1)/Rational(2));
            sample_above = sample_above + (Rational(1)/Rational(2));
        }
        carl::UnivariatePolynomial<Poly> discriminant_u = carl::to_univariate_polynomial(proj.polys()(discriminant), v);
        auto roots_disc = carl::real_roots(discriminant_u, restricted_sample, carl::Interval<Rational>(sample_below, sample_above));
        carl::UnivariatePolynomial<Poly> leading_coeff_u = carl::to_univariate_polynomial(proj.polys()(leading_coeff), v);
        
        // it should not be possible that the discriminant is nullified and it does not matter if the ldcf is nullified.
        assert(roots_disc.is_univariate());
        std::vector<RAN> roots = roots_disc.roots();
        // Find suitable samples
        if (roots.size() > 0) {
            std::size_t ub_index = 0;
            while (ub_index < roots.size() && roots[ub_index] < sample()[v]) ub_index++;
            if (ub_index < roots.size()) {
                // if the discriminant has a root at the actual sample, we cannot find two good samples, so we skip this level
                if (roots[ub_index] == sample()[v]) continue;
                sample_above = carl::sample_between(sample()[v], roots[ub_index]);
            }
            if (ub_index > 0) sample_below = carl::sample_between(roots[ub_index-1], sample()[v]);

            auto roots_ldcf = carl::real_roots(leading_coeff_u, restricted_sample, carl::Interval<Rational>(sample_below, sample()_above));
            if (roots_ldcf.is_univariate()) {
                roots = roots_ldcf.roots();
                ub_index = 0;
                while (ub_index < roots.size() && roots[ub_index] < sample()[v]) ub_index++;
                if (ub_index < roots.size()) {
                    if (roots[ub_index] == sample()[v]) continue; // TODO: does this even happen?
                    sample_above = carl::sample_between(sample()[v], roots[ub_index]);
                }
                if (ub_index > 0) sample_below = carl::sample_between(roots[ub_index-1],sample()[v]);
            }
        }
        // calculate roots corresponding to samples
        restricted_sample.erase(var());
        restricted_sample[v] = sample_below;
        RAN root_at_sample_below = carl::real_roots(poly, restricted_sample).roots()[p.index-1];
        Rational apx_root_below = carl::branching_point(root_at_sample_below);
        restricted_sample[v] = sample_above;
        RAN root_at_sample_above = carl::real_roots(poly, restricted_sample).roots()[p.index-1];
        Rational apx_root_above = carl::branching_point(root_at_sample_above);
        Rational direction_gradient = (apx_root_above - apx_root_below) / (sample_above - sample_below);
        result = result - direction_gradient*(Poly(v) - Poly(carl::branching_point(sample()[v]))); // TODO: branching point only approximates ...
    }
    return IR(proj.polys()(result), 1);
}*/

template<>
IR CellApproximator::apx_between<ApxPoly::SIMPLE>(const IR& p_l, const IR& p_u, const RAN& l, const RAN& u) {
    return IR(proj().polys()(Poly(var()) - approximate_root<ApxSettings::root>(l,u,false)), 1);
}

IR CellApproximator::approximate_bound(const IR& p, const RAN& bound, bool below) {
    #ifdef SMTRAT_DEVOPTION_Statistics
        OCApproximationStatistics::get_instance().degreeReplaced(proj().degree(p.poly));
    #endif
    criteria::ApxCriteria_Detail::get_instance().inform_apx();
    return apx_bound<ApxSettings::bound>(p, bound, below);
}

IR CellApproximator::approximate_between(const IR& p_l, const IR& p_u, const RAN& l, const RAN& u) {
    #ifdef SMTRAT_DEVOPTION_Statistics
        OCApproximationStatistics::get_instance().degreeReplaced(std::max(proj().degree(p_l.poly), proj().degree(p_u.poly)));
    #endif
    return apx_between<ApxSettings::between>(p_l, p_u, l, u);
}

datastructures::CellDescription CellApproximator::compute_cell() {
    if (del().is_section()) { // Section case as before
        return datastructures::CellDescription(util::simplest_bound(proj(), del().lower()->second));
    } else if (del().lower_unbounded() && del().upper_unbounded()) {
        return datastructures::CellDescription(datastructures::Bound::infty, datastructures::Bound::infty);
    } else if (del().lower_unbounded()) {
        IR upper = util::simplest_bound(proj(), del().upper()->second);
        if (criteria::single(proj(), upper))
            upper = approximate_bound(upper, del().upper()->first, false);
        return datastructures::CellDescription(datastructures::Bound::infty, upper);
    } else if (del().upper_unbounded()) {
        IR lower = util::simplest_bound(proj(), del().lower()->second);
        if (criteria::single(proj(), lower))
            lower = approximate_bound(lower, del().lower()->first, true);
        return datastructures::CellDescription(lower, datastructures::Bound::infty);
    } else {
        IR lower = util::simplest_bound(proj(), del().lower()->second);
        IR upper = util::simplest_bound(proj(), del().upper()->second);
        if (criteria::single(proj(), upper))
            upper = approximate_bound(upper, del().upper()->first, false);
        if (criteria::single(proj(), lower))
            lower = approximate_bound(lower, del().lower()->first, true);
        return datastructures::CellDescription(lower, upper);
    }
}

}