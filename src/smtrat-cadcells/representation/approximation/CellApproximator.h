#include "ApproximationSettings.h"
#include "ran_approximation.h"
#include "criteria.h"

namespace smtrat::cadcells::representation::approximation {

using IR = datastructures::IndexedRoot;

class CellApproximator {
    private:
        datastructures::Projections& m_r_proj;
        const datastructures::DelineationInterval& m_r_cell;
        const datastructures::Delineation& m_r_del;
        carl::Variable m_var;
        Assignment m_sample;

        datastructures::Projections& proj() {return m_r_proj;}
        const datastructures::DelineationInterval& cell() const {return m_r_cell;}
        const datastructures::Delineation& del() const {return m_r_del;}
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
        : m_r_proj(der->proj()), m_r_cell(der->cell()), m_r_del(der->delin()), m_var(der->main_var()),
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
    Poly gradient = carl::substitute(derivative, var(), Poly(approximate_RAN(bound)));
    if (gradient.isZero()) return apx_bound<ApxPoly::SIMPLE>(p, bound, below);
    return IR(proj().polys()(gradient*Poly(var()) - gradient*approximate_root<ApxSettings::root>(main_sample(),bound,below)), 1);
}

template<>
IR CellApproximator::apx_bound<ApxPoly::TAYLOR>(const IR& p, const RAN& bound, bool below) {
    assert(apx_settings().taylor_deg < proj().degree(p.poly));
    assert(apx_settings().taylor_deg <= 2);
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
        OCApproximationStatistics::get_instance().taylorIgnoredVars(leftOutVars, dim);
    #endif
    auto apx_sample = sample_root;
    //for (const auto& [key, value] : sample_root) apx_sample[key] = approximate_RAN_sb(value);

    auto one_step_differentiate = [&var_order, &apx_sample, &sample_new_root, dim] (const Poly& poly, Poly& result, std::vector<Poly>& jacobian) {
        Rational evaluated_deriv = 0;
        for (std::size_t i = 0; i < dim; i++) {
            // Skip variables with irrational assignment, since (x_i - s_i) cannot be used
            if (!sample_new_root[var_order[i]].is_numeric()) continue;
            jacobian[i] = carl::derivative(poly, var_order[i]);
            evaluated_deriv = approximate_RAN(*carl::evaluate(jacobian[i], apx_sample));
            if (evaluated_deriv.get_den() != 1) {
                // find approximate value with smaller representation
                Rational ub = evaluated_deriv * (Rational(10001)/Rational(10000));
                Rational lb = evaluated_deriv * (Rational(9999)/Rational(10000));
                Rational c = carl::ceil(evaluated_deriv);
                Rational f = carl::floor(evaluated_deriv);
                if (lb > ub) {
                    std::swap(lb,ub);
                }
                if (c < ub) evaluated_deriv = c;
                else if (lb < f) evaluated_deriv = f;
                else evaluated_deriv = carl::sample_stern_brocot(RationalInterval(lb,ub), false);
            }            
            result = result + Poly(evaluated_deriv) * (Poly(var_order[i]) - Poly(sample_new_root[var_order[i]].value()));
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
    if ((apx_settings().taylor_deg < 2) && (jacobian_sign == 0)) {
        // in this case, p and p' have a common root at s => disc(p)(s_1,...,s_{n-1}) = 0
        // => the next level is a section => should choose artificial root close to actual root?
        // however, we do not actually use p'(s), but an approximation?
        #ifdef SMTRAT_DEVOPTION_Statistics
            OCApproximationStatistics::get_instance().taylorFailure();
        #endif
        return apx_bound<ApxPoly::SIMPLE>(p, bound, below);
    }
    // second order
    if (apx_settings().taylor_deg == 2) {
        int hessian_sign = 0;
        for (std::size_t i = 0; i < dim; i++) {
            if (!sample_new_root[var_order[i]].is_numeric()) continue;
            std::vector<Poly> hessian_row(dim);
            Poly res_i;
            hessian_sign = one_step_differentiate(jacobian[i], res_i, hessian_row);
            result = result + (Poly(Rational(1)/Rational(2)) * (Poly(var_order[i]) - Poly(sample_new_root[var_order[i]].value())) * res_i); 
        }
        if (hessian_sign == 0 && jacobian_sign == 0) {
            #ifdef SMTRAT_DEVOPTION_Statistics
                OCApproximationStatistics::get_instance().taylorFailure();
            #endif
            return apx_bound<ApxPoly::SIMPLE>(p, bound, below);
        } else if (hessian_sign*jacobian_sign == 1) {
            return IR(proj().polys()(result), 2);
        }
    }
    return IR(proj().polys()(result), 1);
}

template<>
IR CellApproximator::apx_bound<ApxPoly::TAYLOR_LIN>(const IR& p, const RAN& bound, bool below) {
    assert(apx_settings().taylor_deg < proj().degree(p.poly));
    assert(apx_settings().taylor_deg <= 2);
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
        OCApproximationStatistics::get_instance().taylorIgnoredVars(leftOutVars, dim);
    #endif
    auto apx_sample = sample_root;
    for (const auto& [key, value] : sample_root) apx_sample[key] = approximate_RAN_sb(value);

    auto one_step_differentiate = [&var_order, &apx_sample, &sample_new_root] (const Poly& poly, Poly& result, std::vector<Poly>& jacobian, std::size_t d) {
        Rational evaluated_deriv = 0;
        for (std::size_t i = 0; i < d; i++) {
            // Skip variables with irrational assignment, since (x_i - s_i) cannot be used
            if (!sample_new_root[var_order[i]].is_numeric()) continue;
            jacobian[i] = carl::derivative(poly, var_order[i]);
            evaluated_deriv = approximate_RAN(*carl::evaluate(jacobian[i], apx_sample));
            if (evaluated_deriv.get_den() != 1) {
                // find approximate value with smaller representation
                Rational ub = evaluated_deriv * (Rational(10001)/Rational(10000));
                Rational lb = evaluated_deriv * (Rational(9999)/Rational(10000));
                Rational c = carl::ceil(evaluated_deriv);
                Rational f = carl::floor(evaluated_deriv);
                if (lb > ub) {
                    std::swap(lb,ub);
                }
                if (c < ub) evaluated_deriv = c;
                else if (lb < f) evaluated_deriv = f;
                else evaluated_deriv = carl::sample_stern_brocot(RationalInterval(lb,ub), false);
            }            
            result = result + Poly(evaluated_deriv) * (Poly(var_order[i]) - Poly(sample_new_root[var_order[i]].value()));
        }
        // return the sign of the main variable derivative
        if (carl::isZero(evaluated_deriv)) return 0;
        else if (evaluated_deriv > 0) return 1;
        else return -1;
    };
    std::vector<Poly> jacobian(dim);
    Poly result;
    // first order taylor approximation
    int jacobian_sign = one_step_differentiate(proj().polys()(p.poly), result, jacobian, dim);
    if ((jacobian_sign == 0)) {
        #ifdef SMTRAT_DEVOPTION_Statistics
            OCApproximationStatistics::get_instance().taylorFailure();
        #endif
        return apx_bound<ApxPoly::SIMPLE>(p, bound, below);
    }
    // second order
    if (apx_settings().taylor_deg == 2) {
        for (std::size_t i = 0; i < dim-1; i++) {
            if (!sample_new_root[var_order[i]].is_numeric()) continue;
            std::vector<Poly> hessian_row(dim-1);
            Poly res_i;
            one_step_differentiate(jacobian[i], res_i, hessian_row, dim-1);
            result = result + (Poly(Rational(1)/Rational(2)) * (Poly(var_order[i]) - Poly(sample_new_root[var_order[i]].value())) * res_i); 
        }
    }
    return IR(proj().polys()(result), 1);
}

/*template<>
IR CellApproximator::apx_bound<ApxPoly::HYPERPLANE>(const IR& p, const RAN& bound, bool below) {
    std::size_t dimensions =sample().size()-1;
    if (apx_settings().hyperplane_dim != 0) dimensions = std::min(apx_settings().hyperplane_dim, dimensions);
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
IR CellApproximator::apx_bound<ApxPoly::MAXIMIZE>(const IR& p, const RAN& bound, bool below) {
    Rational inner = below ? approximate_RAN_below(main_sample()) : approximate_RAN_above(main_sample());
    Rational outer = below ? approximate_RAN_above(bound) : approximate_RAN_below(bound);

    if (sample().size() < 2) { // lowest level -> just get as close as possible
        return IR(proj().polys()(Poly(var()) - outer), 1);
    }

    Rational extra_root = approximate_root<ApxRoot::FIXED_RATIO>(inner, outer, below);

    carl::Variable lower_var = proj().polys().var_order()[sample().size() - 2];
    auto lower_sample = sample();
    lower_sample.erase(var());
    lower_sample.erase(lower_var);

    bool left_unbounded = false, right_unbounded = false;
    RAN lb = main_sample(), ub = main_sample();
    RAN l, u;
    Rational area = 0, new_area = 0;

    for (std::size_t i = 0; i < apx_settings().maximize_n_iter; i++) {
        carl::UnivariatePolynomial<Poly> bound_as_univariate = carl::to_univariate_polynomial(proj().polys()(p.poly), lower_var);
        lower_sample[var()] = extra_root;
        auto roots_result = carl::real_roots(bound_as_univariate, lower_sample);
        assert(!roots_result.is_nullified());
        std::vector<RAN> roots = roots_result.roots();

        if (roots.empty()) break; // unbounded is good enough

        // find roots closest to sample
        auto it = roots.begin();
        while (it != roots.end() && sample()[lower_var] > *it) it++;

        if (it == roots.begin()) { // left unbounded
            if (right_unbounded) { // there must be a point inbetween giving an unbounded interval
                extra_root = approximate_root<ApxRoot::SIMPLE_REPRESENTATION>(extra_root, outer, below);
                continue;
            } 
            if (left_unbounded && ub > *it) break; // new interval is smaller -> stop

            l = sample()[lower_var];
            u = *it;
            if (!left_unbounded) {
                left_unbounded = true;
                area = 0; // new area will definitely be bigger
            }
        } else if (it == roots.end()) { // right unbounded
            it--;
            if (left_unbounded) { // there must be a point inbetween giving an unbounded interval
                extra_root = approximate_root<ApxRoot::SIMPLE_REPRESENTATION>(extra_root, outer, below);
                continue;
            }
            if (right_unbounded && lb < *it) break; // new interval is smaller -> stop

            u = sample()[lower_var];
            l = *it;
            if (!right_unbounded) {
                right_unbounded = true;
                area = 0; // new area will definitely be bigger
            }
        } else { // bounded from both sides
            if (left_unbounded || right_unbounded) break; // new interval is smaller -> stop
            u = *it;
            it--;
            l = *it;
            if ((l > lb) && (u < ub)) break; // new interval is smaller -> stop
        }

        Rational apx_l = approximate_RAN_below(l);
        Rational apx_u = approximate_RAN_above(u);
        new_area = (extra_root - inner)*(apx_u - apx_l);
        if (below) new_area = -new_area;

        if (new_area <= area) break; // new interval is smaller -> stop
        // otherwise continue with new interval
        area = new_area;
        lb = l;
        ub = u;
        outer = extra_root;
        extra_root = approximate_root<ApxRoot::FIXED_RATIO>(inner, outer, below);
    }
    return IR(proj().polys()(Poly(var()) - outer), 1);
}

template<>
IR CellApproximator::apx_between<ApxPoly::SIMPLE>(const IR& p_l, const IR& p_u, const RAN& l, const RAN& u) {
    return IR(proj().polys()(Poly(var()) - approximate_root<ApxSettings::root>(l,u,false)), 1);
}

IR CellApproximator::approximate_bound(const IR& p, const RAN& bound, bool below) {
    #ifdef SMTRAT_DEVOPTION_Statistics
        OCApproximationStatistics::get_instance().approximated(proj().degree(p.poly));
    #endif
    IR result = apx_bound<ApxSettings::bound>(p, bound, below);
    ApxCriteria::inform(proj().polys()(result.poly), result.index);
    return result;
}

IR CellApproximator::approximate_between(const IR& p_l, const IR& p_u, const RAN& l, const RAN& u) {
    #ifdef SMTRAT_DEVOPTION_Statistics
        OCApproximationStatistics::get_instance().approximated(std::max(proj().degree(p_l.poly), proj().degree(p_u.poly)));
    #endif
    return apx_between<ApxSettings::between>(p_l, p_u, l, u);
}

datastructures::CellDescription CellApproximator::compute_cell() {
    if (cell().is_section()) { // Section case as before
        return datastructures::CellDescription(util::simplest_bound(proj(), cell().lower()->second));
    } else if (cell().lower_unbounded() && cell().upper_unbounded()) {
        return datastructures::CellDescription(datastructures::Bound::infty, datastructures::Bound::infty);
    } else if (cell().lower_unbounded()) {
        IR upper = util::simplest_bound(proj(), cell().upper()->second);
        if (ApxCriteria::side(proj(), upper, cell().upper(), del().roots().end()))
            upper = approximate_bound(upper, cell().upper()->first, false);
        return datastructures::CellDescription(datastructures::Bound::infty, upper);
    } else if (cell().upper_unbounded()) {
        IR lower = util::simplest_bound(proj(), cell().lower()->second);
        if (ApxCriteria::side(proj(), lower, del().roots().begin(), del().roots().end()))
            lower = approximate_bound(lower, cell().lower()->first, true);
        return datastructures::CellDescription(lower, datastructures::Bound::infty);
    } else {
        IR lower = util::simplest_bound(proj(), cell().lower()->second);
        IR upper = util::simplest_bound(proj(), cell().upper()->second);
        if (ApxCriteria::side(proj(), upper, cell().upper(), del().roots().end()))
            upper = approximate_bound(upper, cell().upper()->first, false);
        if (ApxCriteria::side(proj(), lower, del().roots().begin(), cell().upper()))
            lower = approximate_bound(lower, cell().lower()->first, true);
        return datastructures::CellDescription(lower, upper);
    }
}

}