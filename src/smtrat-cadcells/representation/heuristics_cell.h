#include "../operators/properties.h"

#include <carl-common/util/streamingOperators.h>

namespace smtrat::cadcells::representation {

    using carl::operator<<;

template<typename T>
inline void compute_section_all_equational(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response) {
    // TODO sometimes it might be beneficial to not include nullified or nonzero polynomials

    for (const auto& poly : der->delin().nullified()) {
        response.equational.insert(poly);
    }
    for (const auto& poly : der->delin().nonzero()) {
        response.equational.insert(poly);
    }
    for (const auto& [ran,irexprs] : der->delin().roots()) {
        for (const auto& ir : irexprs) {
            if (/*ir.index == 1 &&*/ ir.root.poly != response.description.section_defining().poly) { // add poly only once
                response.equational.insert(ir.root.poly);
            }
        }
    }
}

template<typename T>
void maintain_connectedness(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response, bool enable_weak = false) {
    if (der->contains(operators::properties::cell_connected{der->level()}) && !response.description.is_section() && !response.description.lower().is_infty() && !response.description.upper().is_infty()) {
        if (enable_weak) {
            response.ordering.add_leq(response.description.lower().value(), response.description.upper().value());
        } else {
            response.ordering.add_less(response.description.lower().value(), response.description.upper().value());
        }
    }
}


inline boost::container::flat_map<datastructures::PolyRef, boost::container::flat_set<datastructures::PolyRef>> resultants(const datastructures::IndexedRootOrdering& ordering) {
    boost::container::flat_map<datastructures::PolyRef, boost::container::flat_set<datastructures::PolyRef>> result;
    for (const auto& rel : ordering.data()) {
        for (const auto& p1 : rel.first.polys()) {
            for (const auto& p2 : rel.second.polys()) {
                result.try_emplace(p1).first->second.insert(p2);
                result.try_emplace(p2).first->second.insert(p1);
            }
        }
    }
    return result;
}

inline boost::container::flat_map<datastructures::PolyRef, datastructures::IndexedRoot> roots_below(const datastructures::Delineation& delin, const datastructures::DelineationInterval& interval, bool closest) {
    boost::container::flat_map<datastructures::PolyRef, datastructures::IndexedRoot> result;
    if (!interval.lower_unbounded()) {
        auto it = interval.lower();
        while(true) {
            for (const auto& root : it->second) {
                if (!closest || result.find(root.root.poly) == result.end()) {
                    result.emplace(root.root.poly, root.root);
                }
            }
            if (it != delin.roots().begin()) it--;
            else break;
        }
    }
    return result;
}

inline boost::container::flat_map<datastructures::PolyRef, datastructures::IndexedRoot> roots_above(const datastructures::Delineation& delin, const datastructures::DelineationInterval& interval, bool closest) {
    boost::container::flat_map<datastructures::PolyRef, datastructures::IndexedRoot> result;
    if (!interval.upper_unbounded()) {
        auto it = interval.upper();
        while(it != delin.roots().end()) {
            for (const auto& root : it->second) {
                if (!closest || result.find(root.root.poly) == result.end()) {
                    result.emplace(root.root.poly, root.root);
                }
            }
            it++;
        }
    }
    return result;
}

template<typename T>
void extend_to_projective_ordering(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response) {
    response.ordering.set_projective();

    if (der->cell().lower_unbounded() || der->cell().upper_unbounded()) {
        for (const auto& poly : response.ordering.polys()) {
            response.ordering.set_non_projective(poly);
        }
    } else {
        auto res = resultants(response.ordering);
        auto p_closest_below = roots_below(der->delin(), der->cell(), true);
        auto p_closest_above = roots_above(der->delin(), der->cell(), true);
        auto p_farthest_below = roots_below(der->delin(), der->cell(), false);
        auto p_farthest_above = roots_above(der->delin(), der->cell(), false);

        for (const auto& poly : response.ordering.polys()) {
            bool is_below = p_closest_below.find(poly) != p_closest_below.end();
            bool is_above = p_closest_above.find(poly) != p_closest_above.end();
            assert(is_below || is_above);
            if (is_below && !is_above) {
                std::optional<datastructures::IndexedRoot> other_root;
                for (const auto& other_poly : res.at(poly)) {
                    if (p_closest_above.find(other_poly) != p_closest_above.end()) {
                        other_root = p_closest_above.at(other_poly);
                        break;
                    }
                }

                if (other_root) {
                    response.ordering.add_leq(*other_root, p_farthest_below.at(poly));
                } else {
                    response.ordering.set_non_projective(poly);
                }
            } else if (!is_below && is_above) {
                std::optional<datastructures::IndexedRoot> other_root;
                for (const auto& other_poly : res.at(poly)) {
                    if (p_closest_below.find(other_poly) != p_closest_below.end()) {
                        other_root = p_closest_below.at(other_poly);
                        break;
                    }
                }

                if (other_root) {
                    response.ordering.add_leq(*other_root, p_farthest_above.at(poly));
                } else {
                    response.ordering.set_non_projective(poly);
                }
            }
        }
    }
}

template <>
struct cell<CellHeuristic::BIGGEST_CELL> {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->proj(), der->cell());
        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            // response.ordering = simplest_biggest_cell_ordering(der->proj(), der->delin(), der->cell(), response.description);
            datastructures::Delineation reduced_delineation;
            util::PolyDelineations poly_delins;
            util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            response.ordering = util::simplest_biggest_cell_ordering(der->proj(), reduced_delineation, reduced_cell, response.description);
            for (const auto& poly_delin : poly_delins.data) {
                add_chain_ordering(response.ordering, poly_delin.first, poly_delin.second);
            }
        }
        maintain_connectedness(der, response);
        return response;
    }
};

template <>
struct cell<CellHeuristic::BIGGEST_CELL_PDEL> {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        auto response = cell<CellHeuristic::BIGGEST_CELL>::compute(der);
        extend_to_projective_ordering(der, response);
        return response;
    }
};

template <>
struct cell<CellHeuristic::BIGGEST_CELL_FILTER> {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->proj(), der->cell(), true);
        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            datastructures::Delineation reduced_delineation;
            util::PolyDelineations poly_delins;
            util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            response.ordering = util::simplest_biggest_cell_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, true);
            for (const auto& poly_delin : poly_delins.data) {
                add_biggest_cell_ordering(response.ordering, poly_delin.first, poly_delin.second);
            }
            util::add_local_del_ordering(response.ordering, der->delin(), der->cell(), response.description);
        }
        maintain_connectedness(der, response, true);
        return response;
    }
};

template <>
struct cell<CellHeuristic::CHAIN_EQ> {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->proj(), der->cell());

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            datastructures::Delineation reduced_delineation;
            util::PolyDelineations poly_delins;
            util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
            response.ordering = util::simplest_chain_ordering(der->proj(), reduced_delineation);
            for (const auto& poly_delin : poly_delins.data) {
                add_biggest_cell_ordering(response.ordering, poly_delin.first, poly_delin.second);
            }
        }
        maintain_connectedness(der, response);
        return response;
    }
};

template <>
struct cell<CellHeuristic::LOWEST_DEGREE_BARRIERS_EQ> {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->proj(), der->cell());

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            datastructures::Delineation reduced_delineation;
            util::PolyDelineations poly_delins;
            util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            util::ResultantsCache cache;
            std::tie(response.ordering, response.equational) = util::simplest_ldb_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, false, cache);
            for (const auto& poly_delin : poly_delins.data) {
                add_chain_ordering(response.ordering, poly_delin.first, poly_delin.second);
            }
        }
        maintain_connectedness(der, response);
        return response;
    }
};

template<typename T>
inline datastructures::CellRepresentation<T> compute_cell_lowest_degree_barriers(datastructures::SampledDerivationRef<T>& der, util::ResultantsCache& cache) {
    datastructures::CellRepresentation<T> response(der);
    response.description = util::compute_simplest_cell(der->proj(), der->cell());

    if (der->cell().is_section()) {
        datastructures::Delineation reduced_delineation;
        util::PolyDelineations poly_delins;
        util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
        auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
        std::tie(response.ordering, response.equational) = util::simplest_ldb_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, false, cache);
        for (const auto& poly_delin : poly_delins.data) {
            if (response.equational.contains(poly_delin.first)) continue;
            add_chain_ordering(response.ordering, poly_delin.first, poly_delin.second);
        }

        for (const auto& poly : der->delin().nullified()) {
            response.equational.insert(poly);
        }
        for (const auto& poly : der->delin().nonzero()) {
            response.equational.insert(poly);
        }
    } else { // sector
        datastructures::Delineation reduced_delineation;
        util::PolyDelineations poly_delins;
        util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
        auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
        std::tie(response.ordering, response.equational) = util::simplest_ldb_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, false, cache);
        for (const auto& poly_delin : poly_delins.data) {
            add_chain_ordering(response.ordering, poly_delin.first, poly_delin.second);
        }
    }
    maintain_connectedness(der, response);
    return response;
}

template <>
struct cell<CellHeuristic::LOWEST_DEGREE_BARRIERS> {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        util::ResultantsCache cache;
        return compute_cell_lowest_degree_barriers(der, cache);
    }
};

template <>
struct cell<CellHeuristic::LOWEST_DEGREE_BARRIERS_PDEL> {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        auto response = cell<CellHeuristic::LOWEST_DEGREE_BARRIERS>::compute(der);
        extend_to_projective_ordering(der, response);
        return response;
    }
};

template <>
struct cell<CellHeuristic::LOWEST_DEGREE_BARRIERS_FILTER> {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->proj(), der->cell(), true);

        if (der->cell().is_section()) {
            datastructures::Delineation reduced_delineation;
            util::PolyDelineations poly_delins;
            util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            util::ResultantsCache cache;
            std::tie(response.ordering, response.equational) = util::simplest_ldb_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, true, cache);
            for (const auto& poly_delin : poly_delins.data) {
                if (response.equational.contains(poly_delin.first)) continue;
                add_chain_ordering(response.ordering, poly_delin.first, poly_delin.second);
            }

            for (const auto& poly : der->delin().nullified()) {
                response.equational.insert(poly);
            }
            for (const auto& poly : der->delin().nonzero()) {
                response.equational.insert(poly);
            }
        } else { // sector
            datastructures::Delineation reduced_delineation;
            util::PolyDelineations poly_delins;
            util::decompose(der->delin(), der->cell(), reduced_delineation, poly_delins);
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            util::ResultantsCache cache;
            std::tie(response.ordering, response.equational) = util::simplest_ldb_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, true, cache);
            for (const auto& poly_delin : poly_delins.data) {
                add_chain_ordering(response.ordering, poly_delin.first, poly_delin.second);
            }
            util::add_local_del_ordering(response.ordering, der->delin(), der->cell(), response.description);
        }
        maintain_connectedness(der, response);
        return response;
    }
};

}