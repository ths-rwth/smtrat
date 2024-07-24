#include "ApproximationSettings.h"
#include "ran_approximation.h"
#include "criteria.h"
#include <carl-arith/poly/Conversion.h>

namespace smtrat::cadcells::representation::approximation {

using IR = datastructures::IndexedRoot;

struct Simple {

    template<typename T>
    static IR approximate_bound(const IR& /*bound_re*/,
                         const RAN& bound_value,
                         datastructures::SampledDerivationRef<T>& der,
                         bool below)
    {
        Rational root = approximate_root<ApxSettings::root>(der->main_var_sample(), bound_value, below);
        auto& polys = der->proj().polys();
        Polynomial var_poly = Polynomial(polys.context(),der->main_var());
        return IR(polys(carl::get_denom(root)*var_poly - carl::get_num(root)), 1);
    }

    template<typename T>
    static IR approximate_between(const IR& re_l, const RAN& value_l,
                           const IR& re_u, const RAN& value_u,
                           datastructures::SampledDerivationRef<T>& der,
                           bool below) {
        Rational root = approximate_root<ApxSettings::root>(value_l, value_u, false);
        auto& polys = der->proj().polys();
        Polynomial var_poly = Polynomial(polys.context(),der->main_var());
        return IR(polys(carl::get_denom(root) * var_poly - carl::get_num(root)), 1);
    }
};


struct Taylor {
    template<typename T>
    static IR approximate_bound(const IR& bound_re,
                         const RAN& bound_value,
                         datastructures::SampledDerivationRef<T>& der,
                         bool below) {

        assert(apx_settings().taylor_deg < proj().degree(bound_re.poly));
        assert(apx_settings().taylor_deg <= 2);

        SMTRAT_STATISTICS_CALL(
            OCApproximationStatistics::get_instance().approximated(der->proj().degree(bound_re.poly))
        );

        auto& polys = der->proj().polys();

        Poly carl_poly = carl::convert<Poly,Polynomial>(polys(bound_re.poly));

        auto sample_root = der->sample();
        sample_root[der->main_var()] = bound_value; // TODO : can choose other points here (like the actual sample)
        auto sample_new_root = sample_root;
        sample_new_root[der->main_var()] = RAN(approximate_root<ApxSettings::root>(der->main_var_sample(), bound_value, below));

        #ifdef SMTRAT_DEVOPTION_Statistics
            std::size_t left_out_vars = 0;
            for (const auto& [var, val] : sample_new_root) {
                if (!val.is_numeric()) ++left_out_vars;
            }
            OCApproximationStatistics::get_instance().taylorIgnoredVars(left_out_vars, dim);
        #endif

        auto apx_sample = sample_root;
        //for (const auto& [key, value] : sample_root) apx_sample[key] = approximate_RAN_sb(value);

        std::size_t dim = der->sample().size();
        VariableOrdering var_order = polys.var_order();

        auto one_step_differentiate = [&](const Poly& poly, Poly& result, std::vector<Poly>& jacobian) {
            Rational evaluated_deriv = 0;
            for (std::size_t i = 0; i < dim; i++) {
                // Skip variables with irrational assignment, since (x_i - s_i) cannot be used
                if (!sample_new_root[var_order[i]].is_numeric()) continue;
                jacobian[i] = carl::derivative(poly, var_order[i]);
                evaluated_deriv = approximate_RAN(*carl::evaluate(carl::convert<Polynomial,Poly>(polys.context(),jacobian[i]), apx_sample));
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
            if (carl::is_zero(evaluated_deriv)) return 0;
            else if (evaluated_deriv > 0) return 1;
            else return -1;
        };
    
        std::vector<Poly> jacobian(dim);
        Poly result;

        // first order taylor approximation
        int jacobian_sign = one_step_differentiate(carl_poly, result, jacobian);
        if ((apx_settings().taylor_deg < 2) && (jacobian_sign == 0)) {
            // in this case, p and p' have a common root at s => disc(p)(s_1,...,s_{n-1}) = 0
            // => the next level is a section => should choose artificial root close to actual root?
            // however, we do not actually use p'(s), but an approximation?
            SMTRAT_STATISTICS_CALL(OCApproximationStatistics::get_instance().taylorFailure());
            return Simple::approximate_bound(bound_re, bound_value, der, below);
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
                SMTRAT_STATISTICS_CALL(OCApproximationStatistics::get_instance().taylorFailure());
                return Simple::approximate_bound(bound_re, bound_value, der, below);
            } else if (hessian_sign*jacobian_sign == 1) {
                Polynomial result_lp = carl::convert<Polynomial,Poly>(polys.context(),result);
                return IR(polys(result_lp), 2);
            }
        }

        Polynomial result_lp = carl::convert<Polynomial,Poly>(polys.context(),result);
        return IR(polys(result_lp), 1);
    }
};

/*

template<>
inline IR CellApproximator::apx_bound<ApxPoly::TAYLOR_LIN>(const IR& p, const RAN& bound, bool below) {
    assert(apx_settings().taylor_deg < proj().degree(p.poly));
    assert(apx_settings().taylor_deg <= 2);

    Poly carl_poly = carl::convert<Poly,Polynomial>(proj().polys()(p.poly));

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

    auto one_step_differentiate = [&] (const Poly& poly, Poly& result, std::vector<Poly>& jacobian, std::size_t d) {
        Rational evaluated_deriv = 0;
        for (std::size_t i = 0; i < d; i++) {
            // Skip variables with irrational assignment, since (x_i - s_i) cannot be used
            if (!sample_new_root[var_order[i]].is_numeric()) continue;
            jacobian[i] = carl::derivative(poly, var_order[i]);
            evaluated_deriv = approximate_RAN(*carl::evaluate(carl::convert<Polynomial,Poly>(proj().polys().context(),jacobian[i]), apx_sample));
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
        if (carl::is_zero(evaluated_deriv)) return 0;
        else if (evaluated_deriv > 0) return 1;
        else return -1;
    };
    std::vector<Poly> jacobian(dim);
    Poly result;
    // first order taylor approximation
    int jacobian_sign = one_step_differentiate(carl_poly, result, jacobian, dim);
    if (jacobian_sign == 0) {
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
    Polynomial result_lp = carl::convert<Polynomial,Poly>(proj().polys().context(),result);
    return IR(proj().polys()(result_lp), 1);
}
*/

/*
template<>
inline IR CellApproximator::apx_bound<ApxPoly::MAXIMIZE>(const IR& p, const RAN& bound, bool below) {

    Rational inner = below ? approximate_RAN_below(main_sample()) : approximate_RAN_above(main_sample());
    Rational outer = below ? approximate_RAN_above(bound) : approximate_RAN_below(bound);

    if (sample().size() < 2) { // lowest level -> just get as close as possible
        return IR(proj().polys()(carl::get_denom(outer) * Polynomial(proj().polys().context(), var()) - carl::get_num(outer)), 1);
    }

    Rational extra_root = approximate_root<ApxRoot::FIXED_RATIO>(inner, outer, below);

    RAN lower_var_value = sample()[proj().polys().var_order()[sample().size() - 2]];

    bool left_unbounded = false, right_unbounded = false;
    RAN lb = main_sample(), ub = main_sample();
    RAN l, u;
    Rational area = 0, new_area = 0;

    for (std::size_t i = 0; i < apx_settings().maximize_n_iter; i++) {
        Polynomial artificial_bound = carl::get_denom(extra_root) * Polynomial(proj().polys().context(),var()) - carl::get_num(extra_root);
        Polynomial res = carl::resultant(artificial_bound, proj().polys()(p.poly));
        carl::RealRootsResult<RAN> roots_result = carl::real_roots(res, sample());
        assert(!roots_result.is_nullified());
        std::vector<RAN> roots = roots_result.roots();

        if (roots.empty()) break; // unbounded is good enough

        // find roots closest to sample
        auto it = roots.begin();
        while (it != roots.end() && lower_var_value > *it) it++;

        if (it == roots.begin()) { // left unbounded
            if (right_unbounded) { // there must be a point inbetween giving an unbounded interval
                extra_root = approximate_root<ApxRoot::SIMPLE_REPRESENTATION>(extra_root, outer, below);
                continue;
            } 
            if (left_unbounded && ub > *it) break; // new interval is smaller -> stop

            l = lower_var_value;
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

            u = lower_var_value;
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
    return IR(proj().polys()(carl::get_denom(outer) * Polynomial(proj().polys().context(),var()) - carl::get_num(outer)), 1);
}
*/

}