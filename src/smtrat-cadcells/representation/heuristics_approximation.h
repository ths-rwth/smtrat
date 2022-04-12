namespace smtrat::cadcells::representation {

using IR = datastructures::IndexedRoot;

enum ApproximationStrategy {ONLY_BOUNDS, BETWEEN}; // For CHAIN, only BETWEEN makes sense, for LDB we might need another option
enum PolynomialApproximation {SIMPLE, LINEAR_GRADIENT, LINEAR_GRADIENT_MULTI};
enum ApproximationRoot {MEAN, WEIGHTED_MEAN, MAXIMIZE};

struct ApproximationSettings {
    static constexpr std::size_t max_approximations = 100;
    static constexpr ApproximationStrategy strategy = ApproximationStrategy::BETWEEN;
    static constexpr std::size_t critical_degree = 5;
    static constexpr PolynomialApproximation poly = PolynomialApproximation::SIMPLE;
    static constexpr ApproximationRoot root = ApproximationRoot::MEAN;
    static constexpr double root_weight = 0.5;
};

    namespace approximation_criteria {
        bool stop() {
            static std::size_t n_approximations = 0;
            if (n_approximations < ApproximationSettings::max_approximations) {
                n_approximations++;
                return false;
            }
            return true;
        }

        bool single(datastructures::Projections& proj, const IR& ir) {
            return proj.degree(ir.poly) > ApproximationSettings::critical_degree;
        }

        bool pair(datastructures::Projections& proj, const IR& ir_l, const IR& ir_u) {
            return proj.degree(ir_l.poly) + proj.degree(ir_u.poly) > ApproximationSettings::critical_degree;
        }
        template <typename T>
        bool all(datastructures::SampledDerivationRef<T>& der) {
            assert(false); // TODO
            return false;
        }
    }

template<ApproximationRoot AR>
Rational approximate_root(const RAN& l, const RAN& u);

template<>
Rational approximate_root<ApproximationRoot::MEAN>(const RAN& l, const RAN& u) {
    return carl::sample_between(l,u);
}

template<PolynomialApproximation PA>
IR approximate_bound(datastructures::Projections& proj, const IR& p, const RAN& l, const RAN& u, const carl::Variable var);

template<>
IR approximate_bound<PolynomialApproximation::SIMPLE>(datastructures::Projections& proj, const IR& p, const RAN& l, const RAN& u, const carl::Variable var) {
    return IR(proj.polys()(Poly(var) - approximate_root<ApproximationSettings::root>(l,u)), 1);
}

template<PolynomialApproximation PA>
IR approximate_between(datastructures::Projections& proj, const IR& p_l, const IR& p_u, const RAN& l, const RAN& u, const carl::Variable var);

template<>
IR approximate_between<PolynomialApproximation::SIMPLE>(datastructures::Projections& proj, const IR& p_l, const IR& p_u, const RAN& l, const RAN& u, const carl::Variable var) {
    return IR(proj.polys()(Poly(var) - approximate_root<ApproximationSettings::root>(l,u)), 1);
}

datastructures::CellDescription compute_cell(datastructures::Projections& proj, const datastructures::DelineationInterval& del, const carl::Variable var, const RAN& sample) {
    if (del.is_section()) {
        return datastructures::CellDescription(util::simplest_bound(proj, del.lower()->second));
    } else if (del.lower_unbounded() && del.upper_unbounded()) {
        return datastructures::CellDescription(datastructures::Bound::infty, datastructures::Bound::infty);
    } else if (del.lower_unbounded() ) {
        IR bound = util::simplest_bound(proj, del.upper()->second);
        if (approximation_criteria::single(proj, bound))
            return datastructures::CellDescription(datastructures::Bound::infty, approximate_bound<ApproximationSettings::poly>(proj, bound, sample, del.upper()->first, var));
        else return datastructures::CellDescription(datastructures::Bound::infty, bound);
    } else if (del.upper_unbounded()) {
        IR bound = util::simplest_bound(proj, del.lower()->second);
        if (approximation_criteria::single(proj, bound))
            return datastructures::CellDescription(approximate_bound<ApproximationSettings::poly>(proj, bound, del.lower()->first, sample, var), datastructures::Bound::infty);
        else return datastructures::CellDescription(bound, datastructures::Bound::infty);
    } else {
        IR ir_lower = util::simplest_bound(proj, del.lower()->second);
        IR ir_upper = util::simplest_bound(proj, del.upper()->second);
        if (approximation_criteria::single(proj, ir_upper))
            ir_upper = approximate_bound<ApproximationSettings::poly>(proj, ir_upper, sample, del.upper()->first, var);
        if (approximation_criteria::single(proj, ir_lower))
            ir_lower = approximate_bound<ApproximationSettings::poly>(proj, ir_lower, del.lower()->first, sample, var);
        return datastructures::CellDescription(ir_lower, ir_upper);
    }
}

template <>
struct cell<CellHeuristic::BIGGEST_CELL_APPROXIMATION> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        if (approximation_criteria::stop()) return cell<BIGGEST_CELL>::compute(der);

        datastructures::CellRepresentation<T> response(*der);
        if (ApproximationSettings::strategy == ApproximationStrategy::ONLY_BOUNDS) {
            response.description = compute_cell(der->proj(), der->cell(), der->main_var(), der->main_var_sample());
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
                            if (ApproximationSettings::strategy == ApproximationStrategy::BETWEEN) {
                                if (approximation_criteria::pair(der->proj(), ir, *response.description.lower())) {
                                    // TODO: what if the two root expressions correspond to the same root?
                                    IR ir_between = approximate_between<ApproximationSettings::poly>(der->proj(), ir, *response.description.lower(), it->first, der->cell().lower()->first, der->main_var());
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
                            if (ApproximationSettings::strategy == ApproximationStrategy::BETWEEN) {
                                if (approximation_criteria::pair(der->proj(), *response.description.upper(), ir)) {
                                    IR ir_between = approximate_between<ApproximationSettings::poly>(der->proj(), *response.description.upper(), ir, der->cell().upper()->first, it->first, der->main_var());
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