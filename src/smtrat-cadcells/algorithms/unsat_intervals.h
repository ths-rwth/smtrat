#pragma once

#include <vector>

namespace smtrat::cadcells::algorithms {

template <cadcells::operators::op op>
std::vector<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>> get_unsat_intervals(const Constraint& c, datastructures::Projections& proj, const Assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", c << ", " << sample);
    
    auto vars = proj.polys().var_order();
    auto current_var = vars[sample.size()];
    auto tmp_sample = sample;

    assert(carl::level_of(c.lhs()) == sample.size()+1);

    auto deriv = datastructures::make_derivation<typename operators::PropertiesSet<op>::type>(proj, sample, sample.size() + 1).delineated_ref();

    if (carl::is_strict(c.relation())) {
        deriv->insert(operators::properties::poly_semi_sgn_inv{ proj.polys()(c.lhs()) });
    } else {
        deriv->insert(operators::properties::poly_sgn_inv{ proj.polys()(c.lhs()) });
    }
    if (!operators::project_basic_properties<op>(*deriv)) return std::vector<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>>();
    operators::delineate_properties<op>(*deriv);

    std::vector<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>> results;
    auto& roots = deriv->delin().roots(); 
    SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got roots " << roots);
    if (roots.empty()) {
        tmp_sample.insert_or_assign(current_var, RAN(0));
        if (!carl::evaluate(c, tmp_sample)) {
            results.emplace_back(datastructures::make_sampled_derivation<typename operators::PropertiesSet<op>::type>(deriv,RAN(0)));
            SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
            assert(results.back()->cell().lower_unbounded());
            assert(results.back()->cell().upper_unbounded());
        }
    } else {
        if (carl::is_strict(c.relation())) {
            /* This block is needed if
            * the operator does not support weak_sgn_inv
            * a strict constraint is only violated at a single point
            */
            for (auto root = roots.begin(); root != roots.end(); root++) {
                results.emplace_back(datastructures::make_sampled_derivation(deriv, root->first));
                SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
                assert(results.back()->cell().is_section());
            }
        }

        {
            auto current_sample = RAN(carl::sample_below(roots.begin()->first));
            tmp_sample.insert_or_assign(current_var, current_sample);
            if (c.relation() == carl::Relation::EQ || (c.relation() != carl::Relation::NEQ && !carl::evaluate(c, tmp_sample))) {
                results.emplace_back(datastructures::make_sampled_derivation(deriv, current_sample));
                SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
                assert(results.back()->cell().is_sector());
                assert(results.back()->cell().lower_unbounded());
            }
        }
        
        for (auto root = roots.begin(); root != std::prev(roots.end()); root++) {
            auto current_sample = carl::sample_between(root->first, std::next(root)->first);
            tmp_sample.insert_or_assign(current_var, current_sample);
            if (c.relation() == carl::Relation::EQ || (c.relation() != carl::Relation::NEQ && !carl::evaluate(c, tmp_sample))) {
                results.emplace_back(datastructures::make_sampled_derivation(deriv, current_sample));
                SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
                assert(results.back()->cell().is_sector());
                assert(!results.back()->cell().lower_unbounded());
                assert(!results.back()->cell().upper_unbounded());
            }
        }
        
        {
            auto current_sample = RAN(carl::sample_above((--roots.end())->first));
            tmp_sample.insert_or_assign(current_var, current_sample);
            if (c.relation() == carl::Relation::EQ || (c.relation() != carl::Relation::NEQ && !carl::evaluate(c, tmp_sample))) {
                results.emplace_back(datastructures::make_sampled_derivation(deriv, current_sample));
                SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
                assert(results.back()->cell().is_sector());
                assert(results.back()->cell().upper_unbounded());
            }
        }
    }
    return results;
}

template <cadcells::operators::op op>
std::vector<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>> get_unsat_intervals(const VariableComparison& c, datastructures::Projections& proj, const Assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", c << ", " << sample);

    auto vars = proj.polys().var_order();
    auto current_var = vars[sample.size()];
    auto tmp_sample = sample;

    assert(c.var() == current_var);
    assert(std::holds_alternative<RAN>(c.value()) || carl::level_of(std::get<MultivariateRoot>(c.value()).poly()) == sample.size() + 1);

    auto deriv = datastructures::make_derivation<typename operators::PropertiesSet<op>::type>(proj, sample, sample.size() + 1).delineated_ref();

    auto value_result = [&]() -> std::variant<std::pair<datastructures::IndexedRoot, RAN>, datastructures::PolyRef> {
        if (std::holds_alternative<RAN>(c.value())) {
            assert(false);
            RAN root = std::get<RAN>(c.value());
            auto p = carl::defining_polynomial(c);
            auto poly = proj.polys()(p);
            auto poly_roots = proj.real_roots(sample, poly);
            size_t index = (size_t)std::distance(poly_roots.begin(), std::find(poly_roots.begin(), poly_roots.end(), root)) + 1;
            datastructures::IndexedRoot iroot(poly, index);
            return std::make_pair(iroot, root);
        } else {
            auto eval_res = carl::evaluate(std::get<MultivariateRoot>(c.value()), sample);
            if (!eval_res) {
                auto p = carl::defining_polynomial(c);
                return proj.polys()(p);
            } else {
                RAN root = *eval_res;
                auto p = carl::defining_polynomial(c);
                datastructures::IndexedRoot iroot(proj.polys()(p), std::get<MultivariateRoot>(c.value()).k());
                return std::make_pair(iroot, root);
            }
        }
    }();

    std::vector<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>> results;

    if (std::holds_alternative<std::pair<datastructures::IndexedRoot, RAN>>(value_result)) {
        datastructures::IndexedRoot& iroot = std::get<std::pair<datastructures::IndexedRoot, RAN>>(value_result).first;
        RAN& root = std::get<std::pair<datastructures::IndexedRoot, RAN>>(value_result).second;

        auto relation = c.negated() ? carl::inverse(c.relation()) : c.relation();
        bool point = relation == carl::Relation::GREATER || relation == carl::Relation::LESS || relation == carl::Relation::NEQ;
        bool below = relation == carl::Relation::GREATER || relation == carl::Relation::GEQ || relation == carl::Relation::EQ;
        bool above = relation == carl::Relation::LESS || relation == carl::Relation::LEQ || relation == carl::Relation::EQ;

        deriv->insert(operators::properties::poly_pdel{ iroot.poly });
        deriv->insert(operators::properties::root_well_def{ iroot }); // TODO reicht das??
        // if (carl::is_strict(relation)) {
        //     deriv->insert(operators::properties::root_semi_inv{ iroot });
        // } else {
        //     deriv->insert(operators::properties::root_inv{ iroot });
        // }
        // if (!operators::project_basic_properties<op>(*deriv)) return std::vector<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>>();
        // operators::delineate_properties<op>(*deriv);
        deriv->delin().add_root(root, datastructures::TaggedIndexedRoot{iroot, carl::is_strict(relation)});

        if (point) {
            results.emplace_back(datastructures::make_sampled_derivation(deriv, root));
            SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
        }
        if (below) {
            results.emplace_back(datastructures::make_sampled_derivation(deriv, RAN(carl::sample_below(root))));
            SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
        }
        if (above) {
            results.emplace_back(datastructures::make_sampled_derivation(deriv, RAN(carl::sample_above(root))));
            SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
        }
    } else {
        datastructures::PolyRef& poly = std::get<datastructures::PolyRef>(value_result);
        if (proj.is_nullified(sample, poly)) {
            deriv->insert(operators::properties::poly_irreducible_sgn_inv{ poly });
            deriv->delin().add_poly_nullified(poly);
        } else if (proj.num_roots(sample, poly) == 0) {
            // deriv->insert(operators::properties::poly_pdel{ poly });
            deriv->insert(operators::properties::poly_irreducible_sgn_inv{ poly });
            deriv->delin().add_poly_nonzero(poly);
        } else {
            assert(proj.num_roots(sample, poly) > 0 && proj.num_roots(sample, poly) < std::get<MultivariateRoot>(c.value()).k());
            deriv->insert(operators::properties::poly_pdel{ poly });
            deriv->insert(operators::properties::poly_sgn_inv{ deriv->proj().ldcf(poly) });
        }
        results.emplace_back(datastructures::make_sampled_derivation(deriv, RAN(0)));
        SMTRAT_LOG_TRACE("smtrat.cadcells.algorithms.onecell", "Got interval " << results.back()->cell() << " wrt " << results.back()->delin());
    }
    return results;
}

/**
 * Returns the unsat intervals of the given atom w.r.t. an underlying sample.
 * 
 * @param c A constraint or a variable comparison.
 * @param sample A sample point such that the highest variable in @ref c w.r.t. the variable odering in @ref proj is the only unassigned variable.
 * @return A list of sampled derivations with the same delineated derivations. The samples for the unassigned variables are sampled from the respective interval.
 */
template <cadcells::operators::op op>
std::vector<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>> get_unsat_intervals(const Atom& c, datastructures::Projections& proj, const Assignment& sample) {
    SMTRAT_LOG_FUNC("smtrat.cadcells.algorithms.onecell", c << ", " << sample);
    if (std::holds_alternative<Constraint>(c)) {
        return get_unsat_intervals<op>(std::get<Constraint>(c), proj, sample);
    } else if (std::holds_alternative<VariableComparison>(c)) {
        return get_unsat_intervals<op>(std::get<VariableComparison>(c), proj, sample);
    } else {
        assert(false);
        return std::vector<datastructures::SampledDerivationRef<typename operators::PropertiesSet<op>::type>>();
    }
}

}