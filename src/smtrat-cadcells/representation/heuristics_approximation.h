namespace smtrat::cadcells::representation {

using IR = datastructures::IndexedRoot;

enum ApxStrategy {ONLY_BOUNDS, BETWEEN}; // For CHAIN, only BETWEEN makes sense, for LDB we might need another option
enum ApxPoly {
    SIMPLE,
    LINEAR_GRADIENT,
    LINEAR_GRADIENT_MULTI,
    UNIVARIATE_TAYLOR,
    MULTIVARIATE_TAYLOR,
    HYPERPLANE
};
enum ApxRoot {SAMPLE_MID, STERN_BROCOT, FIXED_RATIO, MAXIMIZE};

struct ApxSettings {
    static constexpr std::size_t max_apx = 100;
    static constexpr ApxStrategy strategy = ApxStrategy::ONLY_BOUNDS;
    static constexpr std::size_t critical_degree = 5;
    static constexpr ApxPoly poly = ApxPoly::HYPERPLANE;
    static constexpr std::size_t taylor_deg = 2;
    static constexpr std::size_t hyperplane_dim = 0;
    static constexpr ApxRoot root = ApxRoot::SAMPLE_MID;
    static constexpr std::size_t n_sb_iterations = 1;
    static constexpr double root_ratio = 0.5;
};

namespace approximation_criteria {
    bool stop() {
        static std::size_t n_apx = 0;
        if (n_apx < ApxSettings::max_apx) {
            n_apx++;
            return false;
        }
        return true;
    }

    bool single(datastructures::Projections& proj, const IR& ir) {
        return proj.degree(ir.poly) > ApxSettings::critical_degree;
    }

    bool pair(datastructures::Projections& proj, const IR& ir_l, const IR& ir_u) {
        return proj.degree(ir_l.poly) + proj.degree(ir_u.poly) > ApxSettings::critical_degree;
    }
    template <typename T>
    bool all(datastructures::SampledDerivationRef<T>& der) {
        assert(false); // TODO
        return false;
    }
}

Rational mediant(Rational a, Rational b) {
    return Rational(a.get_num()+b.get_num(), a.get_den()+b.get_den());
}

Rational approximate_RAN_below(const RAN& r, Rational lb) { // TODO: make this good
    Rational mid = carl::branching_point(r);
    if (mid < r) return mid;
    Rational floored = carl::floor(r);
    Rational res;
    while (floored < r) {
        res = floored;
        floored = mediant(floored, mid);
    }
    return res;
}

Rational approximate_RAN_above(const RAN& r, Rational ub) { // TODO: make this good
    Rational mid = carl::branching_point(r);
    if (mid > r) return mid;
    Rational ceiled = carl::ceil(r);
    Rational res;
    while (ceiled > r) {
        res = ceiled;
        ceiled = mediant(mid, ceiled);
    }
    return res;
}

// inner is closer to the sample point
template<ApxRoot AR>
Rational approximate_root(const RAN& inner, const RAN& outer, bool below);

template<>
Rational approximate_root<ApxRoot::SAMPLE_MID>(const RAN& inner, const RAN& outer, bool below) {
    return below ? carl::sample_between(outer, inner) : carl::sample_between(inner, outer);
}

template<>
Rational approximate_root<ApxRoot::STERN_BROCOT>(const RAN& inner, const RAN& outer, bool below) {
    Rational apx_inner = carl::branching_point(inner); // TODO: this could be on the wrong side of the ran
    while(below ? (apx_inner < outer) : (apx_inner > outer)) {
        inner.refine();
        apx_inner = carl::branching_point(inner);
    }
    Rational apx_outer = carl::branching_point(outer);
    // TODO: find smaller representations for apx_inner and apx_outer
    Rational result = apx_inner;
    for (std::size_t i = 0; i < ApxSettings::n_sb_iterations; i++)
        result = mediant(result, apx_outer);
    return result;
}

template<>
Rational approximate_root<ApxRoot::FIXED_RATIO>(const RAN& inner, const RAN& outer, bool below) {
    Rational apx_inner = carl::branching_point(inner); // TODO: this could be on the wrong side of the ran
    while(below ? (apx_inner < outer) : (apx_inner > outer)) {
        inner.refine();
        apx_inner = carl::branching_point(inner);
    }
    Rational apx_outer = carl::branching_point(outer);
    // TODO: find smaller representations for apx_inner and apx_outer
    return (ApxSettings::root_ratio * apx_outer) + ((1 - ApxSettings::root_ratio) * apx_inner); // can lead to ugly large numbers in the rational description
}

class CellApproximator {
    private:
        datastructures::Projections& proj;
        datastructures::DelineationInterval del;
        carl::Variable var;
        Assignment sample;
        RAN main_sample;
    public:
        template<typename T>
        CellApproximator(datastructures::SampledDerivationRef<T>& der) 
        : proj(der->proj()), del(der->cell()), var(der->main_var()),
          sample(der->sample()), main_sample(der->main_var_sample()) {}

        template<ApxPoly PA>
        IR approximate_bound(const IR& p, const RAN& bound, bool below);

        template<ApxPoly PA>
        IR approximate_between(const IR& p_l, const IR& p_u, const RAN& l, const RAN& u);

        datastructures::CellDescription compute_cell();
};

template<>
IR CellApproximator::approximate_bound<ApxPoly::SIMPLE>(const IR& p, const RAN& bound, bool below) {
    #ifdef SMTRAT_DEVOPTION_Statistics
        OCApproximationStatistics::get_instance().degreeReplaced(proj.degree(p.poly));
    #endif
    return IR(proj.polys()(Poly(var) - approximate_root<ApxSettings::root>(main_sample,bound,below)), 1);
}

template<>
IR CellApproximator::approximate_bound<ApxPoly::LINEAR_GRADIENT>(const IR& p, const RAN& bound, bool below) {
    #ifdef SMTRAT_DEVOPTION_Statistics
        OCApproximationStatistics::get_instance().degreeReplaced(proj.degree(p.poly));
    #endif
    Poly derivative = carl::derivative(proj.polys()(p.poly), var);
    auto apx_point = sample;
    apx_point[var] = bound;
    auto gradient = carl::evaluate(derivative, apx_point);
    assert(gradient);
    Rational approximate_gradient = carl::branching_point(*gradient);
    return IR(proj.polys()(approximate_gradient*Poly(var) - approximate_gradient*Poly(approximate_root<ApxSettings::root>(main_sample,bound,below))), 1);
}

template<>
IR CellApproximator::approximate_bound<ApxPoly::LINEAR_GRADIENT_MULTI>(const IR& p, const RAN& bound, bool below) {
    #ifdef SMTRAT_DEVOPTION_Statistics
        OCApproximationStatistics::get_instance().degreeReplaced(proj.degree(p.poly));
    #endif
    Poly derivative = carl::derivative(proj.polys()(p.poly), var);
    Poly gradient = carl::substitute(derivative, var, Poly(carl::branching_point(bound)));
    // p.poly should be irreducible => this gradient is != 0 at the sample 
    return IR(proj.polys()(gradient*Poly(var) - gradient*approximate_root<ApxSettings::root>(main_sample,bound,below)), 1);
}

template<>
IR CellApproximator::approximate_bound<ApxPoly::UNIVARIATE_TAYLOR>(const IR& p, const RAN& bound, bool below) {
    #ifdef SMTRAT_DEVOPTION_Statistics
        OCApproximationStatistics::get_instance().degreeReplaced(proj.degree(p.poly));
    #endif
    // TODO
    assert(false);
    // evaluate p on the lower levels of the sample, then approximate the resulting univariate poly
}

template<>
IR CellApproximator::approximate_bound<ApxPoly::HYPERPLANE>(const IR& p, const RAN& bound, bool below) {
    #ifdef SMTRAT_DEVOPTION_Statistics
        OCApproximationStatistics::get_instance().degreeReplaced(proj.degree(p.poly));
    #endif
    std::size_t dimensions = sample.size()-1;
    if (ApxSettings::hyperplane_dim != 0) dimensions = std::min(ApxSettings::hyperplane_dim, dimensions);
    assert(dimensions > 0); // TODO!!!
    datastructures::PolyRef discriminant = proj.disc(p.poly);
    datastructures::PolyRef leading_coeff = proj.ldcf(p.poly);
    carl::UnivariatePolynomial<Poly> poly = carl::to_univariate_polynomial(proj.polys()(p.poly), var);
    VariableOrdering var_order = proj.polys().var_order();
    Poly result = Poly(var) - Poly(approximate_root<ApxSettings::root>(main_sample, bound, below));
    for (std::size_t i = 1; i <= dimensions; i++) {
        carl::Variable v = var_order[sample.size()-i -1];
        auto restricted_sample = sample;
        restricted_sample.erase(v);
        Rational sample_below = carl::floor(sample[v]);
        Rational sample_above = carl::ceil(sample[v]);
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
            while (ub_index < roots.size() && roots[ub_index] < sample[v]) ub_index++;
            if (ub_index < roots.size()) {
                // if the discriminant has a root at the actual sample, we cannot find two good samples, so we skip this level
                if (roots[ub_index] == sample[v]) continue;
                sample_above = carl::sample_between(sample[v], roots[ub_index]);
            }
            if (ub_index > 0) sample_below = carl::sample_between(roots[ub_index-1], sample[v]);

            auto roots_ldcf = carl::real_roots(leading_coeff_u, restricted_sample, carl::Interval<Rational>(sample_below, sample_above));
            if (roots_ldcf.is_univariate()) {
                roots = roots_ldcf.roots();
                ub_index = 0;
                while (ub_index < roots.size() && roots[ub_index] < sample[v]) ub_index++;
                if (ub_index < roots.size()) {
                    if (roots[ub_index] == sample[v]) continue; // TODO: does this even happen?
                    sample_above = carl::sample_between(sample[v], roots[ub_index]);
                }
                if (ub_index > 0) sample_below = carl::sample_between(roots[ub_index-1], sample[v]);
            }
        }
        // calculate roots corresponding to samples
        restricted_sample.erase(var);
        restricted_sample[v] = sample_below;
        RAN root_at_sample_below = carl::real_roots(poly, restricted_sample).roots()[p.index-1];
        Rational apx_root_below = carl::branching_point(root_at_sample_below);
        restricted_sample[v] = sample_above;
        RAN root_at_sample_above = carl::real_roots(poly, restricted_sample).roots()[p.index-1];
        Rational apx_root_above = carl::branching_point(root_at_sample_above);
        Rational direction_gradient = (apx_root_above - apx_root_below) / (sample_above - sample_below);
        result = result - direction_gradient*(Poly(v) - Poly(carl::branching_point(sample[v]))); // TODO: branching point only approximates ...
    }
    return IR(proj.polys()(result), 1);
}

template<>
IR CellApproximator::approximate_between<ApxPoly::SIMPLE>(const IR& p_l, const IR& p_u, const RAN& l, const RAN& u) {
    #ifdef SMTRAT_DEVOPTION_Statistics
        OCApproximationStatistics::get_instance().degreeReplaced(std::max(proj.degree(p_l.poly), proj.degree(p_u.poly)));
    #endif
    return IR(proj.polys()(Poly(var) - approximate_root<ApxSettings::root>(l,u,false)), 1);
}

datastructures::CellDescription CellApproximator::compute_cell() {
    if (del.is_section()) { // Section case as before
        return datastructures::CellDescription(util::simplest_bound(proj, del.lower()->second));
    } else if (del.lower_unbounded() && del.upper_unbounded()) {
        return datastructures::CellDescription(datastructures::Bound::infty, datastructures::Bound::infty);
    } else if (del.lower_unbounded() ) {
        IR upper = util::simplest_bound(proj, del.upper()->second);
        if (approximation_criteria::single(proj, upper))
            upper = approximate_bound<ApxSettings::poly>(upper, del.upper()->first, false);
        return datastructures::CellDescription(datastructures::Bound::infty, upper);
    } else if (del.upper_unbounded()) {
        IR lower = util::simplest_bound(proj, del.lower()->second);
        if (approximation_criteria::single(proj, lower))
            lower = approximate_bound<ApxSettings::poly>(lower, del.lower()->first, true);
        return datastructures::CellDescription(lower, datastructures::Bound::infty);
    } else {
        IR lower = util::simplest_bound(proj, del.lower()->second);
        IR upper = util::simplest_bound(proj, del.upper()->second);
        if (approximation_criteria::single(proj, upper))
            upper = approximate_bound<ApxSettings::poly>(upper, del.upper()->first, false);
        if (approximation_criteria::single(proj, lower))
            lower = approximate_bound<ApxSettings::poly>(lower, del.lower()->first, true);
        return datastructures::CellDescription(lower, upper);
    }
}


template <>
struct cell<CellHeuristic::BIGGEST_CELL_APPROXIMATION> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        if (approximation_criteria::stop() || der->level() <= 1) return cell<BIGGEST_CELL>::compute(der);

        CellApproximator apx(der);

        datastructures::CellRepresentation<T> response(*der);
        if (ApxSettings::strategy == ApxStrategy::ONLY_BOUNDS) {
            response.description = apx.compute_cell();
        } else {
            response.description = compute_simplest_cell(der->proj(), der->cell());
        }

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            if (!der->delin().nullified().empty()) return std::nullopt;
            // instead of only approximating the cell bounds, we could insert approximations in the following part
            // res(p,q) for high degree polynoimals p,q would be replaced by res(p,r) and res(r,q)
            // this leads to more polynomials than in the other approximation, but the immedeate cell bounds might be more accurate
            if (!der->cell().lower_unbounded()) {
                auto it = der->cell().lower();
                while(true) {
                    for (const auto& ir : it->second) {
                        if (ir != *response.description.lower()) {
                            if (ApxSettings::strategy == ApxStrategy::BETWEEN) {
                                if (approximation_criteria::pair(der->proj(), ir, *response.description.lower())) {
                                    // TODO: what if the two root expressions correspond to the same root?
                                    IR ir_between = apx.approximate_between<ApxSettings::poly>(ir, *response.description.lower(), it->first, der->cell().lower()->first);
                                    response.ordering.add_below(*response.description.lower(), ir_between);
                                    response.ordering.add_below(ir_between, ir); // from here on, this is technically no longer in the biggest-cell-structure
                                } else response.ordering.add_below(*response.description.lower(), ir);
                            } else response.ordering.add_below(*response.description.lower(), ir);
                        } 
                    }
                    if (it != der->delin().roots().begin()) it--;
                    else break;
                }
            }
            if (!der->cell().upper_unbounded()) {
                auto it = der->cell().upper();
                while(it != der->delin().roots().end()) {
                    for (const auto& ir : it->second) {
                        if (ir != *response.description.upper()) {
                            if (ApxSettings::strategy == ApxStrategy::BETWEEN) {
                                if (approximation_criteria::pair(der->proj(), *response.description.upper(), ir)) {
                                    // TODO: what if the two root expressions correspond to the same root?
                                    IR ir_between = apx.approximate_between<ApxSettings::poly>(*response.description.upper(), ir, der->cell().upper()->first, it->first);
                                    response.ordering.add_above(*response.description.upper(), ir_between);
                                    response.ordering.add_above(ir_between, ir); // from here on, this is technically no longer in the biggest-cell-structure
                                } else response.ordering.add_above(*response.description.upper(), ir);
                            } else response.ordering.add_above(*response.description.upper(), ir);
                            response.ordering.add_above(*response.description.upper(), ir);
                        }
                    }
                    it++;
                }
            }
        }
        return response;
    }
};

}