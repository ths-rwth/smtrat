namespace smtrat::cadcells::representation {
    template<typename T>
    std::vector<datastructures::SampledDerivationRef<T>> compute_min_derivs(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
        std::vector<datastructures::SampledDerivationRef<T>> sorted_derivs;
        for (auto& der : derivs) sorted_derivs.emplace_back(der);

        std::sort(sorted_derivs.begin(), sorted_derivs.end(), [](const datastructures::SampledDerivationRef<T>& p_cell1, const datastructures::SampledDerivationRef<T>& p_cell2) { // cell1 < cell2
            const auto& cell1 = p_cell1->cell();
            const auto& cell2 = p_cell2->cell();
            return lower_lt_lower(cell1, cell2) || (lower_eq_lower(cell1, cell2) && upper_lt_upper(cell2, cell1));
        });

        std::vector<datastructures::SampledDerivationRef<T>> min_derivs;
        auto iter = sorted_derivs.begin();
        while (iter != sorted_derivs.end()) {
            min_derivs.emplace_back(*iter);
            auto& last_cell = (*iter)->cell();
            iter++; 
            while (iter != sorted_derivs.end() && !upper_lt_upper(last_cell, (*iter)->cell())) iter++;
        }

        return min_derivs;
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

    template <>
    struct covering<CoveringHeuristic::BIGGEST_CELL_COVERING> {
        template<typename T>
        static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
            datastructures::CoveringRepresentation<T> result;
            auto min_derivs = compute_min_derivs(derivs);
            for (auto& iter : min_derivs) {
                datastructures::CellRepresentation<T> cell_result = cell<BIGGEST_CELL>::compute(iter);
                result.cells.emplace_back(cell_result);
            }
            result.ordering = compute_default_ordering(result.cells);
            return result;
        }
    };

    template <>
    struct covering<CoveringHeuristic::LDB_COVERING> {
        template<typename T>
        static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
            datastructures::CoveringRepresentation<T> result;
            auto min_derivs = compute_min_derivs(derivs);
            result.ordering = compute_default_ordering(result.cells);
            for (auto& iter : min_derivs) {
                datastructures::CellRepresentation<T> cell_result = compute_cell_lowest_degree_barriers(iter, LocalDelMode::NONE, false, false);
                result.cells.emplace_back(cell_result);
                result.ordering = cell_result.ordering;
            }
            return result;
        }
    };

    template <>
    struct covering<CoveringHeuristic::LDB_COVERING_CACHE> {
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

    template <>
    struct covering<CoveringHeuristic::LDB_COVERING_CACHE_GLOBAL> {
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

    template <>
    struct covering<CoveringHeuristic::BIGGEST_CELL_COVERING_PDEL> {
        template<typename T>
        static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
            datastructures::CoveringRepresentation<T> result;
            auto min_derivs = compute_min_derivs(derivs);
            for (auto& iter : min_derivs) {
                datastructures::CellRepresentation<T> cell_result = cell<BIGGEST_CELL_PDEL>::compute(iter);
                result.cells.emplace_back(cell_result);
            }
            result.ordering = compute_default_ordering(result.cells);
            result.ordering.set_projective();
            return result;
        }
    };

    template <>
    struct covering<CoveringHeuristic::BIGGEST_CELL_COVERING_FILTER> {
        template<typename T>
        static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
            datastructures::CoveringRepresentation<T> result;
            auto min_derivs = compute_min_derivs(derivs);
            for (auto& iter : min_derivs) {
                datastructures::CellRepresentation<T> cell_result = cell<BIGGEST_CELL_FILTER>::compute(iter);
                result.cells.emplace_back(cell_result);
            }
            result.ordering = compute_default_ordering(result.cells, true);
            return result;
        }
    };

    template <>
    struct covering<CoveringHeuristic::BIGGEST_CELL_COVERING_FILTER_ONLY_INDEPENDENT> {
        template<typename T>
        static datastructures::CoveringRepresentation<T> compute(const std::vector<datastructures::SampledDerivationRef<T>>& derivs) {
            datastructures::CoveringRepresentation<T> result;
            auto min_derivs = compute_min_derivs(derivs);
            for (auto& iter : min_derivs) {
                datastructures::CellRepresentation<T> cell_result = cell<BIGGEST_CELL_FILTER_ONLY_INDEPENDENT>::compute(iter);
                result.cells.emplace_back(cell_result);
            }
            result.ordering = compute_default_ordering(result.cells, true);
            return result;
        }
    };

    namespace util {
        template<typename T>
        struct IntervalCompare {
            inline constexpr bool operator()(const datastructures::SampledDerivationRef<T>& a, const datastructures::SampledDerivationRef<T>& b) const {
                auto cell_a = a->cell();
                auto cell_b = b->cell();
                return datastructures::lower_lt_lower(cell_a, cell_b) || (datastructures::lower_eq_lower(cell_a, cell_b) && datastructures::upper_lt_upper(cell_b, cell_a));
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
    }

    template <>
    struct covering<CoveringHeuristic::BIGGEST_CELL_COVERING_MIN_TDEG> {
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
                datastructures::CellRepresentation<T> cell_result = cell<BIGGEST_CELL>::compute(deriv);
                result.cells.emplace_back(cell_result);
            }
            result.ordering = compute_default_ordering(result.cells);
            return result;
        }
    };

    template <>
    struct covering<CoveringHeuristic::CHAIN_COVERING> {
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
                cell_result.description = util::compute_simplest_cell((iter)->proj(), (iter)->cell());

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
}