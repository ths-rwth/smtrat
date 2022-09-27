#pragma once

namespace smtrat::cadcells::operators::rules {

template<typename P>
void covering_holds(datastructures::DelineatedDerivation<P>& /*deriv*/, const datastructures::CoveringDescription& covering, const datastructures::IndexedRootOrdering& ordering) {
    SMTRAT_LOG_TRACE("smtrat.cadcells.operators.rules", "holds(" << covering << ")");
    for (auto it = covering.cells().begin(); it != covering.cells().end()-1; it++) {
        assert(ordering.holds_transitive(std::next(it)->lower().value(), it->upper().value(), false));
    }
}

}