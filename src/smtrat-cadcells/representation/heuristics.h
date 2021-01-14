#pragma once

#include "../datastructures/representation.h"

namespace smtrat::cadcells::representation {
    struct cell_heuristic {
        DEFAULT
    };

    struct covering_heuristic {
        DEFAULT
    };

    template<typename H, typename T>
    std::optional<datastructures::covering_representation> compute_representation<H> (const std::vector<cell_derivation_ref<T>>& ders);

    template<typename H, typename T>
    std::optional<datastructures::cell_representation> compute_representation<H> (const cell_derivation_ref<T>& der);

    template<typename T>
    std::optional<datastructures::covering_representation> compute_covering_representation<covering_heuristic::DEFAULT> (const std::vector<cell_derivation_ref<T>>& ders) {
        // TODO compute covering
    }

    template<typename T>
    std::optional<datastructures::cell_representation> compute_cell_representation<cell_heuristic::DEFAULT>(const cell_derivation_ref<T>& der) {
        cell_representation response;
        response.cell = compute_simplest_cell(der.delineation());

        if (der.delineation_cell().is_section()) {
            for (const auto& poly : der.delineation().nullified()) {
                response.equational.push_back(poly);
            }
            for (const auto& poly : der.delineation().noroot()) {
                response.equational.push_back(poly);
            }
            for (const auto& [ran,irexprs] : der.delineation().roots()) {
                for (const auto& ir : irexprs) {
                    if (ir.idx == 1 && ir.poly != response.cell.sector_defining().poly) { // add poly only once
                        response.equational.push_back(ir.poly);
                    }
                }
            }
        } else { // sector
            if (!der.delineation().nullified().empty()) return std::nullopt;

            if (!der.delineation_cell().lower_unbounded()) {
                auto it = der.delineation_cell().lower()+1;
                do {
                    it--;
                    for (const auto& ir : *it) {
                        response.ordering.add_below(std::make_pair(response.cell.lower(), ir));
                    }
                } while(it != der.delineation().roots().begin())
            }
            if (!der.delineation_cell().upper_unbounded()) {
                auto it = der.delineation_cell().upper();
                do {
                    for (const auto& ir : *it) {
                        response.ordering.add_above(std::make_pair(response.cell.upper(), ir));
                    }
                    it++;
                } while(it != der.delineation().roots().end())
            }
        }
        return response;
    }

    cell compute_simplest_cell(const delineation& del) {
        if (del.is_section()) {
            return cell(simplest_bound(*del.lower()));
        } else if (del.lower_unbounded() && del.upper_unbounded()) {
            return cell(INFTY, INFTY);
        } else if (del.lower_unbounded() ) {
            return cell(INFTY, simplest_bound(*del.upper()));
        } else if (del.upper_unbounded()) {
            return cell(simplest_bound(*del.lower()), INFTY);
        } else {
            return cell(simplest_bound(*del.lower()), simplest_bound(*del.upper()));
        }
    }

    indexed_root simplest_bound(const std::vector<indexed_root>& bounds) { // TODO later: improve
        assert(!bound.empty());
        return *bounds.begin();
    }


};