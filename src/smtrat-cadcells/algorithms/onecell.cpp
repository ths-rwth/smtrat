#include "onecell.h"

#include "../operators/mccallum.h"


namespace smtrat::cadcells::algorithms {

namespace detail {
    FormulaT to_formula(cell c) {
        // TODO
        return FormulaT(); 
    }
};

std::vector<delineation> get_unsat_intervals(const Poly& p, const properties& props) {
    // TODO check level of polynomial!

    for (const auto& p : polynomials) {
        props->insert(operators::properties::mccallum::sgn_inv(pool(p)));
    }
    operators::project_basic_properties(proj,props,sample);

    // TODO set_sample erst später aufrufen! denn: aus der delineation wollen wir mehrere unsat intervals erzeugen!
    auto cell_delineation = operators::delineate_cell_properties(proj,props,sample);

    // TODO return list of delineations


}

FormulaT onecell(const std::set<Poly>& polynomials, const datastructures::variable_ordering& varorder, const assignment& sample) {
    datastructures::poly_pool pool(varorder);
    datastructures::projections proj(pool);
    //auto props = std::make_shared<operators::properties>(pool, varorder.size());

    std::vector<delineation> unsat_cells;
    for (const auto& p : polynomials) {
        auto props = std::make_shared<operators::properties>(pool, varorder.size());
        unsat_cells.push_back(get_unsat_intervals(p));
        //props->insert(operators::properties::mccallum::sgn_inv(pool(p)));
        // TODO store props somewhere
    }

    auto covering_representative = compute_representation(unsat_cells);
    // TODO merge corresponding props
    // TODO apply covering rule

    FormulasT description;
    while (props->level() > 0) {
        operators::project_basic_properties(proj,props,sample);
        auto delineation = operators::delineate_properties(proj,props,sample);
        auto cell_delineation(delineation, sample[props->level()]);
        auto cell_representation = compute_representation(cell_delineation);
        if (!cell_representation) {
            return FormulaT();
        }
        operators::project_cell_properties(proj,props,sample,cell_delineation,cell_representation);

        description.emplace_back(to_formula(cell_representation.cell));
        props = props->lower();
        pool.clear(props->level()+1);
        proj.clear(props->level()+1);
    }
    
    return FormulaT(carl::FormulaType::AND, std::move(description));
}

}