#include "onecell.h"

#include "../operators/mccallum.h"


namespace smtrat::cadcells::algorithms {

namespace detail {
    FormulaT to_formula(cell c) {
        // TODO
        return FormulaT(); 
    }
};

FormulaT onecell(const std::set<Poly>& polynomials, const datastructures::variable_ordering& varorder, const Model& sample) {
    datastructures::poly_pool pool(varorder);
    datastructures::projections proj(pool);
    auto props = std::make_shared<operators::mccallum::properties>(pool, varorder.size());

    for (const auto& p : polynomials) {
        props->insert(operators::properties::mccallum::sgn_inv(polys(p)));
    }

    FormulasT description;
    while (props->level() > 0) {
        auto cell = operators:mccallum::construct_cell(proj,prop,sample);
        description.emplace_back(to_formula(cell));
        props = props->lower();
        pool.clear(props->level()+1);
        proj.clear(props->level()+1);
    }
    
    return FormulaT(carl::FormulaType::AND, std::move(description));
}

}