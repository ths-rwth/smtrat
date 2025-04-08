#pragma once

namespace smtrat::cadcells::operators::properties {

inline auto get_level(const datastructures::IndexedRootOrdering& ordering) {
    datastructures::level_t level = 0;
    for (const auto& p : ordering.polys()) {
        level = std::max(level, p.base_level);
    }
    return level;
}

inline auto get_level(const datastructures::RootFunction& function) {
    datastructures::level_t level = 0;
    for (const auto& p : function.polys()) {
        level = std::max(level, p.base_level);
    }
    return level;
}

template<typename P>
void insert_root_ordering_holds(P& deriv, const datastructures::IndexedRootOrdering& ordering) { // transform to a rule?
    if (false) {
        deriv.insert(properties::root_ordering_holds{ ordering, get_level(ordering) });
    } else {
        std::vector<datastructures::IndexedRootOrdering> data_by_level;
        data_by_level.resize(get_level(ordering));
        for (const auto& e : ordering.data()) {
            auto lvl = std::max(get_level(e.first), get_level(e.second));
            assert(lvl <= data_by_level.size());
            if (lvl > 0) {
                if (e.is_strict) {
                    data_by_level[lvl-1].add_less(e.first, e.second);
                } else {
                    data_by_level[lvl-1].add_leq(e.first, e.second);
                }
            }
        }
        for (std::size_t i = 0; i < data_by_level.size(); i++) {
            if (!data_by_level[i].data().empty()) {
                if (ordering.is_projective()) {
                    data_by_level[i].set_projective();
                }
                data_by_level[i].biggest_cell_wrt = ordering.biggest_cell_wrt;
                deriv.insert(properties::root_ordering_holds{ data_by_level[i], i+1 });
            }
        }
    }
}

template<typename P>
bool contains_root_ordering_holds(P& deriv, const datastructures::IndexedRootOrdering& ordering) {
    if (false) {
        return deriv.contains(properties::root_ordering_holds{ ordering, get_level(ordering) });
    } else {
        return true;
    }
}
};