namespace smtrat::cadcells::representation {
    template<typename T>
    std::vector<datastructures::SampledDerivationRef<T>> compute_min_ders(const std::vector<datastructures::SampledDerivationRef<T>>& ders) {
        std::vector<datastructures::SampledDerivationRef<T>> sorted_ders;
        for (auto& der : ders) sorted_ders.emplace_back(der);

        std::sort(sorted_ders.begin(), sorted_ders.end(), [](const datastructures::SampledDerivationRef<T>& p_cell1, const datastructures::SampledDerivationRef<T>& p_cell2) { // cell1 < cell2
            const auto& cell1 = p_cell1->cell();
            const auto& cell2 = p_cell2->cell();
            return lower_lt_lower(cell1, cell2) || (lower_eq_lower(cell1, cell2) && upper_lt_upper(cell2, cell1));
        });

        std::vector<datastructures::SampledDerivationRef<T>> min_ders;
        auto iter = sorted_ders.begin();
        while (iter != sorted_ders.end()) {
            min_ders.emplace_back(*iter);
            auto& last_cell = (*iter)->cell();
            iter++; 
            while (iter != sorted_ders.end() && !upper_lt_upper(last_cell, (*iter)->cell())) iter++;
        }

        return min_ders;
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
        static std::optional<datastructures::CoveringRepresentation<T>> compute(const std::vector<datastructures::SampledDerivationRef<T>>& ders) {
            datastructures::CoveringRepresentation<T> result;
            auto min_ders = compute_min_ders(ders);
            for (auto& iter : min_ders) {
                std::optional<datastructures::CellRepresentation<T>> cell_result = cell<BIGGEST_CELL>::compute(iter);
                if (!cell_result) return std::nullopt;
                result.cells.emplace_back(*cell_result);
            }
            result.ordering = compute_default_ordering(result.cells);
            return result;
        }
    };

    template <>
    struct covering<CoveringHeuristic::BIGGEST_CELL_COVERING_EW> {
        template<typename T>
        static std::optional<datastructures::CoveringRepresentation<T>> compute(const std::vector<datastructures::SampledDerivationRef<T>>& ders) {
            datastructures::CoveringRepresentation<T> result;
            auto min_ders = compute_min_ders(ders);
            for (auto& iter : min_ders) {
                std::optional<datastructures::CellRepresentation<T>> cell_result = cell<BIGGEST_CELL_EW>::compute(iter);
                if (!cell_result) return std::nullopt;
                result.cells.emplace_back(*cell_result);
            }
            result.ordering = compute_default_ordering(result.cells, true);
            return result;
        }
    };

    template <>
    struct covering<CoveringHeuristic::CHAIN_COVERING> {
        template<typename T>
        static std::optional<datastructures::CoveringRepresentation<T>> compute(const std::vector<datastructures::SampledDerivationRef<T>>& ders) {
            datastructures::CoveringRepresentation<T> result;
            
            auto min_ders = compute_min_ders(ders);

            datastructures::Delineation delineation;
            util::PolyDelineations poly_delins;
            std::vector<std::size_t> ord_idx;
            for (auto& iter : min_ders) {
                result.cells.emplace_back(iter);
                auto& cell_result = result.cells.back();   
                cell_result.description = util::compute_simplest_cell((iter)->proj(), (iter)->cell());

                if ((iter)->cell().is_section()) {
                    compute_section_all_equational(iter, cell_result);
                    delineation.add_root((iter)->cell().lower()->first,datastructures::TaggedIndexedRoot {cell_result.description.section_defining() });
                } else {
                    ord_idx.push_back(result.cells.size()-1);
                    if (!(iter)->delin().nullified().empty()) return std::nullopt;
                    util::decompose((iter)->delin(), (iter)->cell(), delineation, poly_delins);
                }
            }

            assert (ord_idx.size() > 0); 
            auto& proj = (*min_ders.begin())->proj();
            auto res = util::simplest_chain_ordering(proj, delineation);
            if (!res) return std::nullopt;
            result.ordering = *res;
            for (const auto& poly_delin : poly_delins.data) {
                add_chain_ordering(result.ordering, poly_delin.first, poly_delin.second);
            }
            for (std::size_t idx : ord_idx) {
                result.cells[idx].ordering = result.ordering;
            }
            return result;
        }
    };
}