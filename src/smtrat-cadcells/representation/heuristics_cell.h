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
            if (ir.root.poly != response.description.section_defining().poly) {
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
        for (const auto& poly : response.ordering_polys) {
            response.ordering_non_projective_polys.insert(poly);
        }
    } else {
        auto p_closest_below = roots_below(der->delin(), der->cell(), true);
        auto p_closest_above = roots_above(der->delin(), der->cell(), true);
        auto p_farthest_below = roots_below(der->delin(), der->cell(), false);
        auto p_farthest_above = roots_above(der->delin(), der->cell(), false);

        for (const auto& poly : response.ordering_polys) {
            bool is_below = p_closest_below.find(poly) != p_closest_below.end();
            bool is_above = p_closest_above.find(poly) != p_closest_above.end();
            assert(is_below || is_above);
            if (is_below && !is_above) {
                std::optional<datastructures::IndexedRoot> other_root;
                for (const auto& other_poly : response.ordering.polys(poly)) {
                    if (p_closest_above.find(other_poly) != p_closest_above.end()) {
                        other_root = p_closest_above.at(other_poly);
                        break;
                    }
                }

                if (other_root) {
                    response.ordering.add_leq(*other_root, p_farthest_below.at(poly));
                } else {
                    response.ordering_non_projective_polys.insert(poly);
                }
            } else if (!is_below && is_above) {
                std::optional<datastructures::IndexedRoot> other_root;
                for (const auto& other_poly : response.ordering.polys(poly)) {
                    if (p_closest_below.find(other_poly) != p_closest_below.end()) {
                        other_root = p_closest_below.at(other_poly);
                        break;
                    }
                }

                if (other_root) {
                    response.ordering.add_leq(*other_root, p_farthest_above.at(poly));
                } else {
                    response.ordering_non_projective_polys.insert(poly);
                }
            }
        }
    }
}

template<typename T>
void init_ordering_polys(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response) {
    for (const auto& [k,v] : der->delin().roots()) {
        for (const auto& tir : v) {
            if (!response.equational.contains(tir.root.poly)) {
                response.ordering_polys.insert(tir.root.poly);
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
            datastructures::Delineation reduced_delineation = der->delin();
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            util::PolyDelineations poly_delins;
            util::decompose(reduced_delineation, reduced_cell, poly_delins);
            util::simplest_biggest_cell_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, response.ordering);
            for (const auto& poly_delin : poly_delins.data) {
                chain_ordering(poly_delin.first, poly_delin.second, response.ordering);
            }
        }
        maintain_connectedness(der, response);
        init_ordering_polys(der, response);
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
            compute_section_all_equational(der, response); // TODO also apply local delineability here!
        } else { // sector
            datastructures::Delineation reduced_delineation = der->delin();
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            for (const auto poly : util::get_local_del_polys(reduced_delineation)) {
                util::local_del_ordering(der->proj(), poly, der->underlying_sample(), der->main_var_sample(), reduced_delineation, response.description, response.ordering);
            }
            util::PolyDelineations poly_delins;
            util::decompose(reduced_delineation, reduced_cell, poly_delins);
            util::simplest_biggest_cell_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, response.ordering, true);
            for (const auto& poly_delin : poly_delins.data) {
                chain_ordering(poly_delin.first, poly_delin.second, response.ordering);
            }
        }
        maintain_connectedness(der, response, true);
        init_ordering_polys(der, response);
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
            datastructures::Delineation reduced_delineation = der->delin();
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            util::PolyDelineations poly_delins;
            util::decompose(reduced_delineation, reduced_cell, poly_delins);
            util::simplest_chain_ordering(der->proj(), reduced_delineation, response.ordering);
            for (const auto& poly_delin : poly_delins.data) {
                chain_ordering(poly_delin.first, poly_delin.second, response.ordering);
            }
        }
        maintain_connectedness(der, response);
        init_ordering_polys(der, response);
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
            datastructures::Delineation reduced_delineation = der->delin();
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            util::PolyDelineations poly_delins;
            util::decompose(reduced_delineation, reduced_cell, poly_delins);
            util::simplest_ldb_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, response.ordering, response.equational, false, false);
            for (const auto& poly_delin : poly_delins.data) {
                chain_ordering(poly_delin.first, poly_delin.second, response.ordering);
            }
        }
        maintain_connectedness(der, response);
        init_ordering_polys(der, response);
        return response;
    }
};

template<typename T>
inline datastructures::CellRepresentation<T> compute_cell_lowest_degree_barriers(datastructures::SampledDerivationRef<T>& der, bool use_global_cache, datastructures::IndexedRootOrdering global_ordering = datastructures::IndexedRootOrdering()) {
    datastructures::CellRepresentation<T> response(der);
    response.description = util::compute_simplest_cell(der->proj(), der->cell());
    response.ordering = global_ordering;

    if (der->cell().is_section()) {
        datastructures::Delineation reduced_delineation = der->delin();
        auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
        util::PolyDelineations poly_delins;
        util::decompose(reduced_delineation, reduced_cell, poly_delins);
        util::simplest_ldb_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, response.ordering, response.equational, false, use_global_cache);
        for (const auto& poly_delin : poly_delins.data) {
            if (response.equational.contains(poly_delin.first)) continue;
            chain_ordering(poly_delin.first, poly_delin.second, response.ordering);
        }
        for (const auto& poly : der->delin().nullified()) {
            response.equational.insert(poly);
        }
        for (const auto& poly : der->delin().nonzero()) {
            response.equational.insert(poly);
        }
    } else { // sector
        datastructures::Delineation reduced_delineation = der->delin();
        auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
        util::PolyDelineations poly_delins;
        util::decompose(reduced_delineation, reduced_cell, poly_delins);
        std::cout << reduced_delineation << std::endl;
        util::simplest_ldb_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, response.ordering, response.equational, false, use_global_cache);
        for (const auto& poly_delin : poly_delins.data) {
            std::cout << poly_delin.first << std::endl;
            chain_ordering(poly_delin.first, poly_delin.second, response.ordering);
        }
    }
    maintain_connectedness(der, response);
    init_ordering_polys(der, response);
    return response;
}

template <>
struct cell<CellHeuristic::LOWEST_DEGREE_BARRIERS> {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        return compute_cell_lowest_degree_barriers(der, false);
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
            datastructures::Delineation reduced_delineation(der->delin());
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            for (const auto poly : util::get_local_del_polys(reduced_delineation)) {
                util::simplify(poly, reduced_delineation); // TODO also apply local delineability here! decide where we apply equational constraints though
            }
            util::PolyDelineations poly_delins;
            util::decompose(reduced_delineation, reduced_cell, poly_delins);
            util::simplest_ldb_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, response.ordering, response.equational, true, false);
            for (const auto& poly_delin : poly_delins.data) {
                if (response.equational.contains(poly_delin.first)) continue;
                chain_ordering(poly_delin.first, poly_delin.second, response.ordering);
            }
            for (const auto& poly : der->delin().nullified()) {
                response.equational.insert(poly);
            }
            for (const auto& poly : der->delin().nonzero()) {
                response.equational.insert(poly);
            }
        } else { // sector
            datastructures::Delineation reduced_delineation(der->delin());
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            for (const auto poly : util::get_local_del_polys(reduced_delineation)) {
                util::local_del_ordering(der->proj(), poly, der->underlying_sample(), der->main_var_sample(), reduced_delineation, response.description, response.ordering);
            }
            util::PolyDelineations poly_delins;
            util::decompose(reduced_delineation, reduced_cell, poly_delins);
            util::simplest_ldb_ordering(der->proj(), reduced_delineation, reduced_cell, response.description, response.ordering, response.equational, true, false);
            for (const auto& poly_delin : poly_delins.data) {
                chain_ordering(poly_delin.first, poly_delin.second, response.ordering);
            }
        }
        maintain_connectedness(der, response);
        init_ordering_polys(der, response);
        return response;
    }
};

}