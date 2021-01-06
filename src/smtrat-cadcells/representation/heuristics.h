#pragma once

#include "../datastructures/roots.h"
#include "../datastructures/delination.h"

namespace smtrat::cadcells::representation {

    struct cell_representation {
        cell interval;
        indexed_root_ordering ordering;
        std::vector<poly_ref> equational;
    };

    struct covering_representation {
        covering cover;
        std::vector<cell_representation> cells;
    };

    struct cell_heuristic {
        DEFAULT
    };

    struct covering_heuristic {
        DEFAULT
    };

    template<cell_heuristic H>
    std::optional<covering_representation> compute_representation<H> (const std::vector<delineation>& del) {
        // TODO how to say which cells are chosen, connection to properties object
    }

    template<cell_heuristic H>
    std::optional<cell_representation> compute_representation<H> (const delineation& del);

    std::optional<cell_representation> compute_representation<cell_heuristic::DEFAULT>(const delineation& del) {
        cell_representation response;
        response.cell = compute_simplest_cell(del);

        if (del.is_section()) {
            for (const auto& poly : del.nullified()) {
                response.equational.push_back(poly);
            }
            for (const auto& poly : del.noroot()) {
                response.equational.push_back(poly);
            }
            for (const auto& [ran,irexprs] : del.roots()) {
                for (const auto& ir : irexprs) {
                    if (ir.idx == 1 && ir.poly != response.cell.sector_defining().poly) { // add poly only once
                        response.equational.push_back(ir.poly);
                    }
                }
            }
        } else { // sector
            if (!del.nullified().empty()) return std::nullopt;

            if (!del.lower_unbounded()) {
                auto it = del.lower()+1;
                do {
                    it--;
                    for (const auto& ir : *it) {
                        response.ordering.add_below(std::make_pair(response.cell.lower(), ir));
                    }
                } while(it != del.roots.begin())
            }
            if (!del.upper_unbounded()) {
                auto it = del.upper();
                do {
                    for (const auto& ir : *it) {
                        response.ordering.add_above(std::make_pair(response.cell.upper(), ir));
                    }
                    it++;
                } while(it != del.roots.end())
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

    indexed_root simplest_bound(const std::vector<indexed_root>& bounds) {
        assert(!bound.empty());
        return *bounds.begin();
    }


};