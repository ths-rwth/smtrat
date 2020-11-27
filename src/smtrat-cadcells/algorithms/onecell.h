#pragma once

#include <set>

#include "../datastructures/polynomials.h"
#include "../operators/operators.h"

namespace smtrat::cadcells::algorithms {

void onecell(const std::set<Poly>& polynomials, const var_order& varorder, const Model& sample) {
    ::datastructures::poly_pool<Poly> polys(varorder);
    std::shared_ptr<::operators::mccallum::properties> props = make_shared<>(poly, varorder.size());

    for (const auto& p : polynomials) {
        props->insert(::operators::properties::mccallum::sgn_inv(polys(p)));
    }

    while (props->level() > 0) {
        // TODO


        props = props->lower();
    }
    
}

}
