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
    datastructures::IndexedRootOrdering compute_default_ordering(const std::vector<datastructures::CellRepresentation<T>>& cells) {
        datastructures::IndexedRootOrdering ordering;
        for (auto it = cells.begin(); it != cells.end()-1; it++) {
            ordering.add_leq(std::next(it)->description.lower().value(), it->description.upper().value());
        }
        return ordering;
    }

    template <>
    struct covering<CoveringHeuristic::DEFAULT_COVERING> {
        template<typename T>
        static std::optional<datastructures::CoveringRepresentation<T>> compute(const std::vector<datastructures::SampledDerivationRef<T>>& ders) {
            datastructures::CoveringRepresentation<T> result_smallest;
            datastructures::CoveringRepresentation<T> result_all_closed;
            std::vector<datastructures::SampledDerivationRef<T>> ders_all_closed;

            SMTRAT_LOG_DEBUG("smtrat.covering","Extracting pure closed cells.");
            for (auto& der : ders) {
                bool lower_considtion = der->cell().lower_unbounded() || der->cell().lower_inclusive();
                bool upper_considtion = der->cell().upper_unbounded() || der->cell().upper_inclusive();

                if(lower_considtion && upper_considtion) {
                    SMTRAT_LOG_DEBUG("smtrat.covering"," :: " << der->cell());
                    ders_all_closed.emplace_back(der);
                }
            }

            // First: Test for all closed cover
            bool valid_all_closed = !ders_all_closed.empty();
            if(valid_all_closed) {
                auto min_ders_all_closed = compute_min_ders(ders_all_closed);
                for (auto& iter : min_ders_all_closed) {
                    std::optional<datastructures::CellRepresentation<T>> cell_result = cell<BIGGEST_CELL>::compute(iter);
                    if (!cell_result) {
                        valid_all_closed = false;
                        break;
                    }
                    result_all_closed.cells.emplace_back(*cell_result);
                }
            }

            if(valid_all_closed) {
                result_all_closed.ordering = compute_default_ordering(result_all_closed.cells);
                valid_all_closed = valid_all_closed && result_all_closed.is_valid();
            }

            SMTRAT_LOG_DEBUG("smtrat.covering","Can use pure closed intervals (containing open derivation (-oo;oo)): " << valid_all_closed);
            if(valid_all_closed) return result_all_closed;

            // Second: Default cover
            auto min_ders_smallest = compute_min_ders(ders);
            for (auto& iter : min_ders_smallest) {
                std::optional<datastructures::CellRepresentation<T>> cell_result = cell<BIGGEST_CELL>::compute(iter);
                if (!cell_result) return std::nullopt;
                result_smallest.cells.emplace_back(*cell_result);
            }
            result_smallest.ordering = compute_default_ordering(result_smallest.cells);

            return result_smallest;
        }
    };

    template <>
    struct covering<CoveringHeuristic::CHAIN_COVERING> {
        template<typename T>
        static std::optional<datastructures::CoveringRepresentation<T>> compute(const std::vector<datastructures::SampledDerivationRef<T>>& ders) {
            datastructures::CoveringRepresentation<T> result;
            
            auto min_ders = compute_min_ders(ders);

            datastructures::Delineation delineation;
            std::vector<std::size_t> ord_idx;
            for (auto& iter : min_ders) {
                result.cells.emplace_back(iter);
                auto& cell_result = result.cells.back();   
                cell_result.description = util::compute_simplest_cell((iter)->proj(), (iter)->cell());

                if ((iter)->cell().is_section()) {
                    compute_section_all_equational(iter, cell_result);
                    delineation.add_root((iter)->cell().lower()->first,cell_result.description.section_defining());
                } else {
                    ord_idx.push_back(result.cells.size()-1);

                    if (!(iter)->delin().nullified().empty()) return std::nullopt;

                    // for each cell, only the roots of a poly below and above the cell are relevant
                    if (!(iter)->cell().lower_unbounded()) {
                        boost::container::flat_set<datastructures::PolyRef> ignoring;
                        auto it = (iter)->cell().lower();
                        while(true) {
                            for (const auto& ir : it->second) {
                                if (ignoring.contains(ir.poly)) continue;
                                delineation.add_root(it->first,ir);
                                ignoring.insert(ir.poly);
                            }
                            if (it != (iter)->delin().roots().begin()) it--;
                            else break;
                        }
                    }
                    if (!(iter)->cell().upper_unbounded()) {
                        boost::container::flat_set<datastructures::PolyRef> ignoring;
                        auto it = (iter)->cell().upper();
                        while(it != (iter)->delin().roots().end()) {
                            for (const auto& ir : it->second) {
                                if (ignoring.contains(ir.poly)) continue;
                                delineation.add_root(it->first,ir);
                                ignoring.insert(ir.poly);
                            }
                            it++;
                        }
                    }
                }
            }

            assert (ord_idx.size() > 0); 
            auto& proj = (*min_ders.begin())->proj();
            auto ordering = *util::simplest_delineation_ordering(proj, delineation);
            for (std::size_t idx : ord_idx) {
                result.cells[idx].ordering = ordering;
            }
            result.ordering = ordering;
            return result;
        }
    };
}