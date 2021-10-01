namespace smtrat::cadcells::representation {

std::optional<datastructures::IndexedRoot> simplest_bound(datastructures::Projections& proj, const std::vector<datastructures::IndexedRoot>& bounds, const boost::container::flat_set<datastructures::PolyRef>& ignoring) {
    assert(!bounds.empty());
    auto simplest = bounds.begin();
    for (auto iter = bounds.begin(); iter != bounds.end(); iter++) {
        if (ignoring.contains(iter->poly)) continue;
        if (proj.degree(iter->poly) < proj.degree(simplest->poly)) {
            simplest = iter;
        }
    }
    if (ignoring.contains(bounds.begin()->poly)) return std::nullopt;
    return *simplest;
}

datastructures::IndexedRoot simplest_bound(datastructures::Projections& proj, const std::vector<datastructures::IndexedRoot>& bounds) {
    boost::container::flat_set<datastructures::PolyRef> ignoring;
    return *simplest_bound(proj, bounds, ignoring);
}

datastructures::CellDescription compute_simplest_cell(datastructures::Projections& proj, const datastructures::DelineationInterval& del) {
    if (del.is_section()) {
        return datastructures::CellDescription(simplest_bound(proj, del.lower()->second));
    } else if (del.lower_unbounded() && del.upper_unbounded()) {
        return datastructures::CellDescription(datastructures::Bound::infty, datastructures::Bound::infty);
    } else if (del.lower_unbounded() ) {
        return datastructures::CellDescription(datastructures::Bound::infty, simplest_bound(proj, del.upper()->second));
    } else if (del.upper_unbounded()) {
        return datastructures::CellDescription(simplest_bound(proj, del.lower()->second), datastructures::Bound::infty);
    } else {
        return datastructures::CellDescription(simplest_bound(proj, del.lower()->second), simplest_bound(proj, del.upper()->second));
    }
}

template<typename T>
void compute_section_all_equational(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response) {
    for (const auto& poly : der->delin().nullified()) {
        response.equational.insert(poly);
    }
    for (const auto& poly : der->delin().nonzero()) {
        response.equational.insert(poly);
    }
    for (const auto& [ran,irexprs] : der->delin().roots()) {
        for (const auto& ir : irexprs) {
            if (/*ir.index == 1 &&*/ ir.poly != response.description.section_defining().poly) { // add poly only once
                response.equational.insert(ir.poly);
            }
        }
    }
}

template <>
struct cell<CellHeuristic::BIGGEST_CELL> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(*der);
        response.description = compute_simplest_cell(der->proj(), der->cell());

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            if (!der->delin().nullified().empty()) return std::nullopt;

            if (!der->cell().lower_unbounded()) {
                auto it = der->cell().lower();
                while(true) {
                    for (const auto& ir : it->second) {
                        if (ir != *response.description.lower()) {
                            response.ordering.add_below(*response.description.lower(), ir);
                        } 
                    }
                    if (it != der->delin().roots().begin()) it--;
                    else break;
                }
            }
            if (!der->cell().upper_unbounded()) {
                auto it = der->cell().upper();
                while(it != der->delin().roots().end()) {
                    for (const auto& ir : it->second) {
                        if (ir != *response.description.upper()) {
                            response.ordering.add_above(*response.description.upper(), ir);
                        }
                    }
                    it++;
                }
            }
        }
        return response;
    }
};

template <>
struct cell<CellHeuristic::CHAIN_EQ> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(*der);
        response.description = compute_simplest_cell(der->proj(), der->cell());

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            if (!der->delin().nullified().empty()) return std::nullopt;

            if (!der->cell().lower_unbounded()) {
                boost::container::flat_set<datastructures::PolyRef> ignoring;
                auto it = der->cell().lower();
                while(true) {
                    auto simplest = simplest_bound(der->proj(), it->second, ignoring);
                    if (!simplest) {
                        if (*simplest != *response.description.lower()) {
                            response.ordering.add_below(*response.description.lower(), *simplest);
                        }
                        for (const auto& ir : it->second) {
                            if (ignoring.contains(ir.poly)) continue;
                            if (ir != *simplest) {
                                response.ordering.add_below(*simplest, ir);
                            } 
                            ignoring.insert(ir.poly);
                        }
                    }
                    if (it != der->delin().roots().begin()) it--;
                    else break;
                }
            }
            if (!der->cell().upper_unbounded()) {
                boost::container::flat_set<datastructures::PolyRef> ignoring;
                auto it = der->cell().upper();
                while(it != der->delin().roots().end()) {
                    auto simplest = simplest_bound(der->proj(), it->second, ignoring);
                    if (!simplest) {
                        if (*simplest != *response.description.upper()) {
                            response.ordering.add_above(*response.description.upper(), *simplest);
                        }
                        for (const auto& ir : it->second) {
                            if (ignoring.contains(ir.poly)) continue;
                            if (ir != *simplest) {
                                response.ordering.add_above(*simplest, ir);
                            } 
                            ignoring.insert(ir.poly);
                        }
                    }
                    it++;
                }
            }
        }
        return response;
    }
};

/*
template<typename T>
void compute_sector_barriers(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response) {
    if (!der->cell().lower_unbounded()) {
        auto it = der->cell().lower();
        auto barrier = *response.description.lower();
        while(true) {
            auto old_barrier = barrier;
            auto current_simplest = simplest_bound(der->proj(), it->second);
            if (der->proj().degree(current_simplest.poly) < der->proj().degree(barrier.poly)) {
                barrier = current_simplest;
            }
            assert(it != der->cell().lower() || barrier == *response.description.lower());
            if (barrier != old_barrier) {
                response.ordering.add_below(old_barrier, barrier);
            }
            for (const auto& ir : it->second) {
                if (ir != barrier) {
                    response.ordering.add_below(barrier, ir);
                } 
            }
            if (it != der->delin().roots().begin()) it--;
            else break;
        }
    }
    if (!der->cell().upper_unbounded()) {
        auto it = der->cell().upper();
        auto barrier = *response.description.upper();
        while(it != der->delin().roots().end()) {
            auto old_barrier = barrier;
            auto current_simplest = simplest_bound(der->proj(), it->second);
            if (der->proj().degree(current_simplest.poly) < der->proj().degree(barrier.poly)) {
                barrier = current_simplest;
            }
            assert(it != der->cell().upper() || barrier == *response.description.upper());
            if (barrier != old_barrier) {
                response.ordering.add_above(old_barrier, barrier);
            }
            for (const auto& ir : it->second) {
                if (ir != barrier) {
                    response.ordering.add_above(barrier, ir);
                } 
            }
            it++;
        }
    }
}
*/

template<typename T>
void compute_barriers(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response, bool section) {
    while(section) {
        auto old_size = response.equational.size();

        auto it = der->cell().lower();
        while(true) {
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ir->poly == response.description.section_defining().poly) continue;
                if (response.equational.contains(ir->poly)) continue;
                if (der->proj().degree(ir->poly) >= der->proj().degree(response.description.section_defining().poly)) {
                    response.equational.insert(ir->poly);
                }
            }
            if (it != der->delin().roots().begin()) it--;
            else break;
        }

        it = der->cell().upper();
        while(it != der->delin().roots().end()) {
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ir->poly == response.description.section_defining().poly) continue;
                if (response.equational.contains(ir->poly)) continue;
                if (der->proj().degree(ir->poly) >= der->proj().degree(response.description.section_defining().poly)) {
                    response.equational.insert(ir->poly);
                }
            }
            it++;
        }

        if (old_size == response.equational.size()) {
            break;
        }
    }

    if (!der->cell().lower_unbounded())  {
        boost::container::flat_set<datastructures::PolyRef> ignoring;
        auto it = der->cell().lower();
        auto barrier = *response.description.lower_defining();
        while(true) {
            auto old_barrier = barrier;
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ignoring.contains(ir->poly)) continue;
                if (section && response.equational.contains(ir->poly)) continue;
                if (der->proj().degree(ir->poly) < der->proj().degree(barrier.poly)) {
                    barrier = *ir;
                }
            }
            assert(it != der->cell().lower() || barrier == *response.description.lower_defining());
            if (barrier != old_barrier) {
                response.ordering.add_below(old_barrier, barrier);
            }
            for (const auto& ir : it->second) {
                if (ignoring.contains(ir.poly)) continue;
                if (section && response.equational.contains(ir.poly)) continue;
                if (ir != barrier) {
                    response.ordering.add_below(barrier, ir);
                } 
                ignoring.insert(ir.poly);
            }
            if (it != der->delin().roots().begin()) it--;
            else break;
        }
    }
    if (!der->cell().upper_unbounded()) {
        boost::container::flat_set<datastructures::PolyRef> ignoring;
        auto it = der->cell().upper();
        auto barrier = *response.description.upper_defining();
        while(it != der->delin().roots().end()) {
            auto old_barrier = barrier;
            for (auto ir = it->second.begin(); ir != it->second.end(); ir++) {
                if (ignoring.contains(ir->poly)) continue;
                if (section && response.equational.contains(ir->poly)) continue;
                if (der->proj().degree(ir->poly) < der->proj().degree(barrier.poly)) {
                    barrier = *ir;
                }
            }
            assert(it != der->cell().upper() || barrier == *response.description.upper_defining());
            if (barrier != old_barrier) {
                response.ordering.add_above(old_barrier, barrier);
            }
            for (const auto& ir : it->second) {
                if (ignoring.contains(ir.poly)) continue;
                if (section && response.equational.contains(ir.poly)) continue;
                if (ir != barrier) {
                    response.ordering.add_above(barrier, ir);
                } 
                ignoring.insert(ir.poly);
            }
            it++;
        }
    }
}

template <>
struct cell<CellHeuristic::LOWEST_DEGREE_BARRIERS_EQ> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(*der);
        response.description = compute_simplest_cell(der->proj(), der->cell());

        if (der->cell().is_section()) {
            compute_section_all_equational(der, response);
        } else { // sector
            if (!der->delin().nullified().empty()) return std::nullopt;
            compute_barriers(der, response, false);
        }
        return response;
    }
};


template <>
struct cell<CellHeuristic::LOWEST_DEGREE_BARRIERS> {
    template<typename T>
    static std::optional<datastructures::CellRepresentation<T>> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(*der);
        response.description = compute_simplest_cell(der->proj(), der->cell());

        if (der->cell().is_section()) {
            for (const auto& poly : der->delin().nullified()) {
                response.equational.insert(poly);
            }
            for (const auto& poly : der->delin().nonzero()) {
                response.equational.insert(poly);
            }

            compute_barriers(der, response, true);
        } else { // sector
            if (!der->delin().nullified().empty()) return std::nullopt;
            compute_barriers(der, response, false);
        }
        return response;
    }
};

}