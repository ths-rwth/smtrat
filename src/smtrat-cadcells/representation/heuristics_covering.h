#include "approximation/polynomials.h"

namespace smtrat::cadcells::representation {

template<typename T>
std::vector<datastructures::SampledDerivationRef<T>> compute_min_derivs(const std::vector<datastructures::SampledDerivationRef<T>>& derivs, bool remove_all_redundancies=false) {
    std::vector<datastructures::SampledDerivationRef<T>> sorted_derivs;
    for (auto& der : derivs) sorted_derivs.emplace_back(der);

    std::sort(
        sorted_derivs.begin(), sorted_derivs.end(),
        [](const datastructures::SampledDerivationRef<T>& p_cell1, const datastructures::SampledDerivationRef<T>& p_cell2) {
            // cell1 < cell2
            const auto& cell1 = p_cell1->cell();
            const auto& cell2 = p_cell2->cell();
            return lower_lt_lower(cell1, cell2) || (lower_eq_lower(cell1, cell2) && upper_lt_upper(cell2, cell1));
        }
    );

    std::vector<datastructures::SampledDerivationRef<T>> min_derivs;
    auto iter = sorted_derivs.begin();
    while (iter != sorted_derivs.end()) {
        min_derivs.emplace_back(*iter);
        auto& last_cell = (*iter)->cell();
        iter++; 
        while (iter != sorted_derivs.end() && !upper_lt_upper(last_cell, (*iter)->cell())) iter++;
    }

    if (!remove_all_redundancies || min_derivs.size() < 3) return min_derivs;

    // remove cells covered by the union of the other cells
    // the result is not unique. We greedily (from left to right) remove redundant cells.
    std::vector<datastructures::SampledDerivationRef<T>> min_derivs_irred;

    for (auto it = min_derivs.begin(); it != min_derivs.end(); ) {
        min_derivs_irred.emplace_back(*it);
        auto it2 = std::next(std::next(it));
        while (it2 != min_derivs.end() && !upper_lt_lower((*it)->cell(), (*it2)->cell())) {
            ++it2;
        }
        if (it2 == min_derivs.end()) break;
        it = std::prev(it2);
    }
    
    min_derivs_irred.emplace_back(min_derivs.back());
    return min_derivs_irred;
}

template<typename T>
datastructures::IndexedRootOrdering compute_default_ordering(const std::vector<datastructures::CellRepresentation<T>>& cells, bool enable_weak = false) {
    datastructures::IndexedRootOrdering ordering;
    for (auto it = cells.begin(); it != cells.end()-1; it++) {
        if (enable_weak && (!std::next(it)->description.lower().is_strict() || !it->description.upper().is_strict())) {
            ordering.add_leq(std::next(it)->description.lower().value(), it->description.upper().value());
        } else {
            if (std::next(it)->description.lower().value() == it->description.upper().value()) {
                ordering.add_eq(std::next(it)->description.lower().value(), it->description.upper().value());
            } else {
                ordering.add_less(std::next(it)->description.lower().value(), it->description.upper().value());
            }
            
        }
    }
    return ordering;
}


namespace covering_heuristics {

// ============================== lowest degree barriers ===========================================

struct LDBCovering {
    template<typename T>
    static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        datastructures::CoveringRepresentation<T> result;
        auto min_derivs = compute_min_derivs(derivs);
        for (auto& iter : min_derivs) {
            datastructures::CellRepresentation<T> cell_result = compute_cell_lowest_degree_barriers(iter, LocalDelMode::NONE, false, false);
            result.cells.emplace_back(cell_result);
            result.ordering = cell_result.ordering;
        }
        result.ordering = compute_default_ordering(result.cells);
        return result;
    }
};


struct LDBCoveringCache {
    template<typename T>
    static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        datastructures::CoveringRepresentation<T> result;
        auto min_derivs = compute_min_derivs(derivs);
        datastructures::IndexedRootOrdering tmp_ordering;
        for (auto& iter : min_derivs) {
            datastructures::CellRepresentation<T> cell_result = compute_cell_lowest_degree_barriers(iter, LocalDelMode::NONE, false, false, tmp_ordering);
            result.cells.emplace_back(cell_result);
            tmp_ordering = cell_result.ordering;
        }
        result.ordering = compute_default_ordering(result.cells);
        return result;
    }
};


struct LDBCoveringCacheGlobal {
    template<typename T>
    static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        datastructures::CoveringRepresentation<T> result;
        auto min_derivs = compute_min_derivs(derivs);
        datastructures::IndexedRootOrdering tmp_ordering;
        for (auto& iter : min_derivs) {
            datastructures::CellRepresentation<T> cell_result = compute_cell_lowest_degree_barriers(iter, LocalDelMode::NONE, false, true, tmp_ordering);
            result.cells.emplace_back(cell_result);
            tmp_ordering = cell_result.ordering;
        }
        result.ordering = compute_default_ordering(result.cells);
        return result;
    }
};


// ============================== biggest cell =====================================================

struct BiggestCellCovering {
    template<typename T>
    static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        datastructures::CoveringRepresentation<T> result;
        auto min_derivs = compute_min_derivs(derivs);
        for (auto& iter : min_derivs) {
            datastructures::CellRepresentation<T> cell_result = cell_heuristics::BiggestCell::compute(iter);
            result.cells.emplace_back(cell_result);
        }
        result.ordering = compute_default_ordering(result.cells);
        return result;
    }
};


struct BiggestCellCoveringPdel {
    template<typename T>
    static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        datastructures::CoveringRepresentation<T> result;
        auto min_derivs = compute_min_derivs(derivs);
        for (auto& iter : min_derivs) {
            datastructures::CellRepresentation<T> cell_result = cell_heuristics::BiggestCellPdel::compute(iter);
            result.cells.emplace_back(cell_result);
        }
        result.ordering = compute_default_ordering(result.cells);
        result.ordering.set_projective();
        return result;
    }
};


struct BiggestCellCoveringFilter {
    template<typename T>
    static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        datastructures::CoveringRepresentation<T> result;
        auto min_derivs = compute_min_derivs(derivs);
        for (auto& iter : min_derivs) {
            datastructures::CellRepresentation<T> cell_result = cell_heuristics::BiggestCellFilter::compute(iter);
            result.cells.emplace_back(cell_result);
        }
        result.ordering = compute_default_ordering(result.cells, true);
        return result;
    }
};


struct BiggestCellCoveringFilterOnlyIndependent {
    template<typename T>
    static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        datastructures::CoveringRepresentation<T> result;
        auto min_derivs = compute_min_derivs(derivs);
        for (auto& iter : min_derivs) {
            datastructures::CellRepresentation<T> cell_result = cell_heuristics::BiggestCellFilterOnlyIndependent::compute(iter);
            result.cells.emplace_back(cell_result);
        }
        result.ordering = compute_default_ordering(result.cells, true);
        return result;
    }
};

} // namespace covering_heuristics

namespace util {

template<typename T>
struct IntervalCompare {
    inline constexpr bool operator()(const datastructures::SampledDerivationRef<T>& a, const datastructures::SampledDerivationRef<T>& b) const {
        auto cell_a = a->cell();
        auto cell_b = b->cell();
        return (
            datastructures::lower_lt_lower(cell_a, cell_b) ||
            (datastructures::lower_eq_lower(cell_a, cell_b) && datastructures::upper_lt_upper(cell_b, cell_a))
        );
    }
};

template<typename T>
using DerivationSet = boost::container::flat_set<datastructures::SampledDerivationRef<T>, IntervalCompare<T>>;
template<typename T>
bool is_covering(const DerivationSet<T>& set) {
    if (set.empty()) return false;
    auto current_max = set.end();
    for (auto iter = set.begin(); iter != set.end(); iter++) {
        if (current_max == set.end()) {
            if ((*iter)->cell().lower_unbounded()) {
                current_max = iter;
            } else {
                return false;
            }
        } else {
            if (!datastructures::upper_lt_lower((*current_max)->cell(), (*iter)->cell())) {
                if (datastructures::upper_lt_upper((*current_max)->cell(), (*iter)->cell())) {
                    current_max = iter;
                }
            } else {
                return false;
            }
        }
    }
    return (*current_max)->cell().upper_unbounded();
}

} // namespace util

namespace covering_heuristics {

struct BiggestCellCoveringMinTdeg {
    template<typename T>
    static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        struct Data {
            datastructures::SampledDerivationRef<T> deriv;
            std::size_t tdeg;
            bool nullified;
        };
        std::vector<Data> sorted_by_tdeg;
        for (auto& deriv : derivs) {
            std::size_t tdeg = 0;
            for (const auto& e : deriv->delin().roots()) {
                for (const auto& e2 : e.second) {
                    tdeg = std::max(tdeg, deriv->proj().total_degree(e2.root.poly));
                }
            }
            bool nullified = deriv->cell().is_sector() && !deriv->delin().nullified().empty();
            sorted_by_tdeg.push_back(Data{deriv, tdeg, nullified});
        }
        std::sort(sorted_by_tdeg.begin(), sorted_by_tdeg.end(), [](const Data& a, const Data& b) {
            return  (a.nullified && !b.nullified) || (a.nullified == b.nullified && a.tdeg > b.tdeg);
        });
        util::DerivationSet<T> set(derivs.begin(), derivs.end());
        for (const auto& e : sorted_by_tdeg) {
            set.erase(e.deriv);
            if (!util::is_covering(set)) {
                set.insert(e.deriv);
            }
        }
        assert(util::is_covering(set));
        datastructures::CoveringRepresentation<T> result;
        for (auto& deriv : set) {
            datastructures::CellRepresentation<T> cell_result = cell_heuristics::BiggestCell::compute(deriv);
            result.cells.emplace_back(cell_result);
        }
        result.ordering = compute_default_ordering(result.cells);
        return result;
    }
};


// ============================== chain ============================================================

struct ChainCovering {
    template<typename T>
    static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        datastructures::CoveringRepresentation<T> result;
        
        auto min_derivs = compute_min_derivs(derivs);

        datastructures::Delineation delineation;
        util::PolyDelineations poly_delins;
        std::vector<std::size_t> ord_idx;
        for (auto& iter : min_derivs) {
            result.cells.emplace_back(iter);
            auto& cell_result = result.cells.back();   
            cell_result.description = util::compute_simplest_cell((iter)->level(), (iter)->proj(), (iter)->cell());

            if ((iter)->cell().is_section()) {
                handle_section_all_equational(iter, cell_result);
                delineation.add_root((iter)->cell().lower()->first,datastructures::TaggedIndexedRoot {cell_result.description.section_defining() });
            } else {
                ord_idx.push_back(result.cells.size()-1);
                datastructures::Delineation subdelin = (iter)->delin();
                auto subdelin_int = subdelin.delineate_cell((iter)->main_var_sample());
                util::decompose(subdelin, subdelin_int, poly_delins);
                delineation.merge_with(subdelin);
            }
        }

        assert (ord_idx.size() > 0); 
        auto& proj = (*min_derivs.begin())->proj();
        util::simplest_chain_ordering(proj, delineation, result.ordering);
        for (const auto& poly_delin : poly_delins.data) {
            chain_ordering(poly_delin.first, poly_delin.second, result.ordering);
        }
        for (std::size_t idx : ord_idx) {
            result.cells[idx].ordering = result.ordering;
        }
        return result;
    }
};


// ============================== all compound =====================================================

struct AllCompoundCovering {
    template<typename T>
    static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        datastructures::CoveringRepresentation<T> result;
        auto min_derivs = compute_min_derivs(derivs);
        for (auto& iter : min_derivs) {
            datastructures::CellRepresentation<T> cell_result = cell_heuristics::AllCompound::compute(iter);
            result.cells.emplace_back(cell_result);
        }
        result.ordering = compute_default_ordering(result.cells);
        return result;
    }
};

}

// ============================== approximation ====================================================

namespace approximation {

template<typename Settings, typename T>
void insert_approximations(std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
    if (derivs.size() < 2) return;

    auto it = derivs.begin();
    auto it_next = std::next(it);
    for (; it_next != derivs.end(); ++it, ++it_next) {
        const datastructures::DelineationInterval& cell = (*it)->cell();
        const datastructures::DelineationInterval& next_cell = (*it_next)->cell();
        assert(!cell.upper_unbounded() && !next_cell.lower_unbounded());
        
        // if the cells just touch, we do not want to approximate.
        if (cell.is_section() || next_cell.is_section()) continue;
        if (next_cell.lower()->first == cell.upper()->first) continue;

        // check whether the simplest two boundary-defining polynomials have high degree
        {
            auto ir_l = util::simplest_bound((*it_next)->proj(), next_cell.lower()->second);
            auto ir_u = util::simplest_bound((*it)->proj(), cell.upper()->second);
            if (!Settings::Criteria::get().poly_pair((*it)->proj(), ir_l, ir_u)) continue;
        }

        // calculate new root
        Rational new_root = SampleSimple::above(next_cell.lower()->first, cell.upper()->first); // TODO : Settings?

        // if the new sample is an ugly number, we might want to skip it.
        if (!Settings::Criteria::get().sample(new_root)) continue;

        // construct root expression
        const auto& context = (*it)->proj().polys().context();
        const auto var = (*it)->main_var();
        Polynomial apx_poly = carl::get_denom(new_root)*Polynomial(context,var) - carl::get_num(new_root);
        datastructures::TaggedIndexedRoot new_ire = {
            .root = datastructures::IndexedRoot((*it)->proj().polys()(apx_poly), 1), /* NOTE: all derivs use the same proj */
            .is_inclusive = true
        };

        SMTRAT_LOG_DEBUG(
            "smtrat.covering.apx",
            "Insert new root at " << new_root << " between " << next_cell.lower()->first
            << " and " << cell.upper()->first << " to get " << new_ire << "\n"
        );

        // insert approximation
        (*it)->move_main_var_sample_below(new_root); // make sure the re-delineation works properly
        (*it)->delin().add_root(new_root, new_ire); // this invalidates the iterators for the cell boundaries
        (*it)->delineate_cell();
        (*it_next)->move_main_var_sample_above(new_root); // make sure the re-delineation works properly
        (*it_next)->delin().add_root(new_root, new_ire); // this invalidates the iterators for the cell boundaries
        (*it_next)->delineate_cell();
    }
}

} // namespace approximation

namespace covering_heuristics {

template<typename Settings>
struct BiggestCellAPXCovering {
    template<typename T>
    static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        datastructures::CoveringRepresentation<T> result;
        auto min_derivs = compute_min_derivs(derivs, true);

        if (Settings::Criteria::get().covering()) {
            approximation::insert_approximations<Settings>(min_derivs);
        }

        for (auto& iter : min_derivs) {
            datastructures::CellRepresentation<T> cell_result = cell_heuristics::BiggestCellFilter::compute(iter);
            result.cells.emplace_back(cell_result);
        }
        result.ordering = compute_default_ordering(result.cells, true);
        SMTRAT_LOG_DEBUG("smtrat.covering.apx", "Result: " << result << "\n");
        return result;
    }
};

} // namespace covering_heuristics
} // namespace representation