#include "onecell.h"

#include "../operators/mccallum.h"


namespace smtrat::cadcells::algorithms {

void onecell(const std::set<Poly>& polynomials, const datastructures::variable_ordering& varorder, const Model& sample) {
    datastructures::poly_pool pool(varorder);
    auto props = std::make_shared<operators::mccallum::properties>(pool, varorder.size());

    for (const auto& p : polynomials) {
        props->insert(operators::properties::mccallum::sgn_inv(polys(p)));
    }

    while (props->level() > 0) {
        // TODO


        props = props->lower();
    }
    
}

}