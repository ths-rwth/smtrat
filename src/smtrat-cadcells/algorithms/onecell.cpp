#include "onecell.h"
#include "helper.h"

#include "../operators/mccallum.h"


namespace smtrat::cadcells::algorithms {

namespace detail {
    inline MultivariateRootT as_multivariate_root(const poly_pool& pool, carl::Variable main_var, indexed_root r) {
        const Poly& poly = pool(r.poly);
        assert(poly.gatherVariables().count(main_var) == 1);
        return MultivariateRootT(Poly(carl::UnivariatePolynomial<Poly>(MultivariateRootT::var(), carl::to_univariate_polynomial(poly, main_var).coefficients())), r.idx);
    }

    FormulaT to_formula(const poly_pool& pool, carl::Variable main_var, cell c) {
        if (c.is_section()) {
            return FormulaT(VarComparisonT(main_var, as_multivariate_root(pool,main_var,c.sector_defining()), carl::Relation::EQ));
        } else {
            FormulasT subformulas;
            if (c.lower()) {
                subformulas.emplace_back(VarComparisonT(main_var, as_multivariate_root(pool,main_var,*c.lower()), carl::Relation::GEQ));
            }
            FormulaT lower(carl::FormulaType::TRUE);
            if (c.upper()) {
                subformulas.emplace_back(VarComparisonT(main_var, as_multivariate_root(pool,main_var,*c.upper()), carl::Relation::LEQ));
            }
            return FormulaT(carl::FormulaType::AND, std::move(subformulas));
        } 
    }
};

std::vector<std::shared_ptr<cell_derivation>> get_unsat_intervals(const ConstraintT& c, const projection& proj, const assignment& sample) {
    assert(level_of(vars, c.lhs()) == sample.size()+1);

    auto current_var = vars[sample.size()];
    auto tmp_sample = sample;

    auto deriv = make_derivation<properties<op::mccallum>>(proj, sample);

    deriv->insert(operators::properties::sgn_inv(pool(c.lhs())));
    operators::project_basic_properties<op::mccallum>(deriv);
    operators::delineate_cell_properties<op::mccallum>(deriv);

    std::vector<std::shared_ptr<cell_derivation>> results;
    auto& roots = deriv.delineation().roots(); 
    if (roots.empty()) {
        tmp_sample.insert(current_var, 0);
        if (!carl::evaluate(c, tmp_sample)) {
            results.emplace_back(make_cell_derivation(deriv,0));
        }
    } else {
        results.emplace_back(deriv.delineate_cell(carl::sample_below(roots.front().first)));        
        for (auto root = roots.begin(); root != roots.end(); root++) {
            if (c.relation().isWeak()) {
                results.emplace_back(make_cell_derivation(deriv, root->first));
            }
            
            auto current_sample = carl::sample_between(root->first, (root+1)->first);
            tmp_sample.insert(current_var, 0);
            if (!carl::evaluate(c, tmp_sample)) {
                results.emplace_back(make_cell_derivation(deriv, current_sample));
            }
        }
        if (c.relation().isWeak()) {
            results.emplace_back(make_cell_derivation(deriv, roots.back().first));
        }
        auto current_sample = carl::sample_above(roots.back().first);
        tmp_sample.insert(current_var, 0);
        if (!carl::evaluate(c, tmp_sample)) {
            results.emplace_back(make_cell_derivation(deriv, current_sample));
        }
    }
    return results;
}

FormulaT onecell(const std::set<ConstraintT>& constraints, const datastructures::variable_ordering& vars, const assignment& sample) {
    datastructures::poly_pool pool(vars);
    datastructures::projections proj(pool);

    {
        std::vector<std::shared_ptr<cell_derivation>> unsat_cells;
        for (const auto& c : constraints) {
            unsat_cells.push_back(get_unsat_intervals(c, proj, sample));
        }

        auto covering_representative = compute_representation(unsat_cells);
        if (!covering_representation) {
            return FormulaT();
        }
        // TODO first merge underlying cells
        // TODO then compute covering and project cells
    }

    auto cell_deriv = ...;

    FormulasT description;
    while (props->level() > 0) {
        operators::project_basic_properties(cell_deriv);
        operators::delineate_properties(cell_deriv);
        cell_deriv.set_sample(sample[cell_deriv.main_var()]);
        auto cell_representation = compute_representation(cell_deriv);
        if (!cell_representation) {
            return FormulaT();
        }
        operators::project_cell_properties(cell_deriv,cell_representation);

        description.emplace_back(helper::to_formula(cell_deriv.main_var(),cell_representation.cell));
        cell_deriv = cell_deriv->underlying();
        pool.clear(props->level()+1);
        proj.clear(props->level()+1);
    }

    return FormulaT(carl::FormulaType::AND, std::move(description));
}

}