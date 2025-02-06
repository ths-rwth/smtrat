#pragma once

#include "../operators/properties.h"

#include <carl-common/util/streamingOperators.h>

namespace smtrat::cadcells::representation {

using carl::operator<<;

template<typename T>
inline void handle_section_all_equational(const datastructures::Delineation& delin, datastructures::CellRepresentation<T>& response) {
	// note: sometimes it might be beneficial to not include nullified or nonzero polynomials

	for (const auto& poly : delin.nullified()) {
		response.equational.insert(poly);
	}
	for (const auto& poly : delin.nonzero()) {
		response.equational.insert(poly);
	}
	for (const auto& [ran, irexprs] : delin.roots()) {
		for (const auto& ir : irexprs) {
			if (ir.root.poly != response.description.section_defining().poly) {
				response.equational.insert(ir.root.poly);
			}
		}
	}
}


template<typename T>
void handle_connectedness(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response, bool enable_weak = false) {
    if (der->contains(operators::properties::cell_connected{der->level()})
        && !response.description.is_section()
        && !response.description.lower().is_infty()
        && !response.description.upper().is_infty()
    ) {
        if (enable_weak && response.description.lower().is_weak() && response.description.upper().is_weak()) {
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
		while (true) {
			for (const auto& root : it->second) {
				if (!closest || result.find(root.root.poly) == result.end()) {
					result.emplace(root.root.poly, root.root);
				}
			}
			if (it != delin.roots().begin())
				it--;
			else
				break;
		}
	}
	return result;
}


inline boost::container::flat_map<datastructures::PolyRef, datastructures::IndexedRoot> roots_above(const datastructures::Delineation& delin, const datastructures::DelineationInterval& interval, bool closest) {
	boost::container::flat_map<datastructures::PolyRef, datastructures::IndexedRoot> result;
	if (!interval.upper_unbounded()) {
		auto it = interval.upper();
		while (it != delin.roots().end()) {
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
void handle_projective_ordering(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response) {
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
void handle_ordering_polys(datastructures::SampledDerivationRef<T>& der, datastructures::CellRepresentation<T>& response) {
	for (const auto& [k, v] : der->delin().roots()) {
		for (const auto& tir : v) {
			if (!response.equational.contains(tir.root.poly)) {
				response.ordering_polys.insert(tir.root.poly);
			}
		}
	}
}


template<typename T>
void handle_cell_reduction(datastructures::Delineation& reduced_delineation, datastructures::DelineationInterval& reduced_cell, datastructures::CellRepresentation<T>& response) {
	util::PolyDelineations poly_delins;
	util::decompose(reduced_delineation, reduced_cell, poly_delins);
	for (const auto& poly_delin : poly_delins.data) {
		chain_ordering(poly_delin.first, poly_delin.second, response.ordering);
	}
}


template<typename T>
void handle_local_del(datastructures::SampledDerivationRef<T>& der, datastructures::Delineation& reduced_delineation, datastructures::CellRepresentation<T>& response) {
    for (const auto poly : util::get_local_del_polys(reduced_delineation)) {
        util::local_del_ordering(
            der->proj(), poly, der->underlying_sample(), der->main_var_sample(),
            reduced_delineation, response.description, response.ordering
        );
    }
}


inline void handle_local_del_simplify_all(datastructures::Delineation& reduced_delineation) {
	for (const auto poly : util::get_local_del_polys(reduced_delineation)) {
		util::simplify(poly, reduced_delineation);
	}
}

inline void handle_local_del_simplify_non_independent(datastructures::Delineation& reduced_delineation) {
	for (const auto poly : util::get_local_del_polys(reduced_delineation)) {
		if (!util::local_del_poly_independent(reduced_delineation, poly)) {
			util::simplify(poly, reduced_delineation);
		}
	}
}

enum class LocalDelMode { NONE,
						  ALL,
						  ONLY_INDEPENDENT,
						  SIMPLIFY };


// =========================== biggest cell ========================================================
namespace cell_heuristics {

struct BiggestCell {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->level(), der->proj(), der->cell());
        if (der->cell().is_section()) {
            handle_section_all_equational(der->delin(), response);
        } else { // sector
            datastructures::Delineation reduced_delineation = der->delin();
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            handle_cell_reduction(reduced_delineation, reduced_cell, response);
            util::simplest_biggest_cell_ordering(
                der->proj(), reduced_delineation, reduced_cell,
                response.description, response.ordering
            );
        }
        handle_connectedness(der, response);
        handle_ordering_polys(der, response);
        SMTRAT_STATISTICS_CALL(statistics().got_representation_equational(der->level(), response.equational.size()));
        return response;
    }
};


struct BiggestCellPdel {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        auto response = BiggestCell::compute(der);
        handle_projective_ordering(der, response);
        return response;
    }
};

} // namespace cell_heuristics

template<typename T>
inline datastructures::CellRepresentation<T> compute_cell_biggest_cell(datastructures::SampledDerivationRef<T>& der, LocalDelMode ldel_mode = LocalDelMode::NONE, bool enable_weak = false) {
    datastructures::CellRepresentation<T> response(der);
    datastructures::Delineation reduced_delineation = der->delin();
    if (ldel_mode == LocalDelMode::ONLY_INDEPENDENT) {
        handle_local_del_simplify_non_independent(reduced_delineation);
    } else if (ldel_mode == LocalDelMode::SIMPLIFY) {
        handle_local_del_simplify_all(reduced_delineation);
    }
    auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
    SMTRAT_STATISTICS_CALL(statistics().got_representation_roots_inside(der->level(), reduced_delineation, reduced_cell));
    response.description = util::compute_simplest_cell(der->level(), der->proj(), reduced_cell, enable_weak);
    response.ordering.biggest_cell_wrt = response.description;
    if (der->cell().is_section()) {
        handle_local_del_simplify_non_independent(reduced_delineation);
        handle_local_del(der, reduced_delineation, response);
        handle_section_all_equational(reduced_delineation, response);
    } else { // sector
        handle_local_del(der, reduced_delineation, response);
        handle_cell_reduction(reduced_delineation, reduced_cell, response);
        util::simplest_biggest_cell_ordering(
            der->proj(), reduced_delineation, reduced_cell,
            response.description, response.ordering, enable_weak
        );
    }
    handle_connectedness(der, response, enable_weak);
    handle_ordering_polys(der, response);
    SMTRAT_STATISTICS_CALL(statistics().got_representation_equational(der->level(), response.equational.size()));
    return response;
}


namespace cell_heuristics {

struct BiggestCellFilter {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        return compute_cell_biggest_cell(der, LocalDelMode::ALL, true);
    }
};


struct BiggestCellFilterOnlyIndependent {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        return compute_cell_biggest_cell(der, LocalDelMode::ONLY_INDEPENDENT, true);
    }
};


// =========================== chain ===============================================================

struct ChainEq {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->level(), der->proj(), der->cell());

        if (der->cell().is_section()) {
            handle_section_all_equational(der->delin(), response);
        } else { // sector
            datastructures::Delineation reduced_delineation = der->delin();
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            handle_cell_reduction(reduced_delineation, reduced_cell, response);
            util::simplest_chain_ordering(der->proj(), reduced_delineation, response.ordering);
        }
        handle_connectedness(der, response);
        handle_ordering_polys(der, response);
        SMTRAT_STATISTICS_CALL(
            statistics().got_representation_equational(der->level(), response.equational.size())
        );
        return response;
    }
};


// =========================== lowest degree barriers ==============================================

struct LowestDegreeBarriersEq {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        response.description = util::compute_simplest_cell(der->level(), der->proj(), der->cell());

        if (der->cell().is_section()) {
            handle_section_all_equational(der->delin(), response);
        } else { // sector
            datastructures::Delineation reduced_delineation = der->delin();
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            handle_cell_reduction(reduced_delineation, reduced_cell, response);
            util::simplest_ldb_ordering(
                der->proj(), reduced_delineation, reduced_cell, response.description,
                response.ordering, response.equational, false, false
            );
        }
        handle_connectedness(der, response);
        handle_ordering_polys(der, response);
        SMTRAT_STATISTICS_CALL(statistics().got_representation_equational(der->level(), response.equational.size()));
        return response;
    }
};

} // namespace cell_heuristics

template<typename T>
inline datastructures::CellRepresentation<T> compute_cell_lowest_degree_barriers(datastructures::SampledDerivationRef<T>& der, LocalDelMode ldel_mode = LocalDelMode::NONE, bool enable_weak = false, bool use_global_cache = false, datastructures::IndexedRootOrdering global_ordering = datastructures::IndexedRootOrdering()) {
    datastructures::CellRepresentation<T> response(der);
    datastructures::Delineation reduced_delineation = der->delin();
    if (ldel_mode == LocalDelMode::ONLY_INDEPENDENT) {
        handle_local_del_simplify_non_independent(reduced_delineation);
    } else if (ldel_mode == LocalDelMode::SIMPLIFY) {
        handle_local_del_simplify_all(reduced_delineation);
    }
    auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
    response.description = util::compute_simplest_cell(der->level(), der->proj(), reduced_cell, enable_weak);
    response.ordering = global_ordering;

    if (der->cell().is_section()) {
        handle_local_del_simplify_non_independent(reduced_delineation);
        handle_local_del(der, reduced_delineation, response);
        util::PolyDelineations poly_delins;
        util::decompose(reduced_delineation, reduced_cell, poly_delins);
        util::simplest_ldb_ordering(
            der->proj(), reduced_delineation, reduced_cell, response.description,
            response.ordering, response.equational, enable_weak, use_global_cache
        );
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
        handle_local_del(der, reduced_delineation, response);
        handle_cell_reduction(reduced_delineation, reduced_cell, response);
        util::simplest_ldb_ordering(
            der->proj(), reduced_delineation, reduced_cell, response.description,
            response.ordering, response.equational, enable_weak, use_global_cache
        );
    }
    handle_connectedness(der, response, enable_weak);
    handle_ordering_polys(der, response);
    SMTRAT_STATISTICS_CALL(
        statistics().got_representation_equational(der->level(), response.equational.size())
    );
    return response;
}


namespace cell_heuristics {

struct LowestDegreeBarriers {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        return compute_cell_lowest_degree_barriers(der);
    }
};


struct LowestDegreeBarriersCacheGlobal {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        return compute_cell_lowest_degree_barriers(der, LocalDelMode::NONE, false, true);
    }
};


struct LowestDegreeBarriersPdel {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        auto response = LowestDegreeBarriers::compute(der);
        handle_projective_ordering(der, response);
        return response;
    }
};


struct LowestDegreeBarriersFilter {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        return compute_cell_lowest_degree_barriers(der, LocalDelMode::ALL, true);
    }
};


struct LowestDegreeBarriersFilterOnlyIndependent {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        return compute_cell_lowest_degree_barriers(der, LocalDelMode::ONLY_INDEPENDENT, true);
    }
};


// =========================== all compound ========================================================

struct AllCompound {
    template<typename T>
    static datastructures::CellRepresentation<T> compute(datastructures::SampledDerivationRef<T>& der) {
        datastructures::CellRepresentation<T> response(der);
        if (der->cell().is_section()) {
            response.description = util::compute_simplest_cell(der->level(), der->proj(), der->cell());
            handle_section_all_equational(der->delin(), response);
        } else { // sector
            datastructures::Delineation reduced_delineation = der->delin();
            auto reduced_cell = reduced_delineation.delineate_cell(der->main_var_sample());
            handle_cell_reduction(reduced_delineation, reduced_cell, response);


            datastructures::Bound lower = datastructures::Bound::infty();
            datastructures::Bound upper = datastructures::Bound::infty();
        
            if (!reduced_cell.lower_unbounded()) {
                std::vector<std::vector<datastructures::IndexedRoot>> roots;
                auto it = reduced_cell.lower();
                while(true) {
                    for (const auto& ir : it->second) {
                        roots.emplace_back(std::vector<datastructures::IndexedRoot>({ir.root}));
                    }
                    if (it != reduced_delineation.roots().begin()) it--;
                    else break;
                }
                lower = datastructures::Bound::strict(datastructures::RootFunction(datastructures::CompoundMaxMin{std::move(roots),std::nullopt}));
            }
            if (!reduced_cell.upper_unbounded()) {
                std::vector<std::vector<datastructures::IndexedRoot>> roots;
                auto it = reduced_cell.upper();
                while(it != reduced_delineation.roots().end()) {
                    for (const auto& ir : it->second) {
                        roots.emplace_back(std::vector<datastructures::IndexedRoot>({ir.root}));
                    }
                    it++;
                }
                upper = datastructures::Bound::strict(datastructures::RootFunction(datastructures::CompoundMinMax{std::move(roots),std::nullopt}));
            }

            response.description = datastructures::SymbolicInterval(lower, upper);
            
        }
        handle_connectedness(der, response);
        handle_ordering_polys(der, response);
        SMTRAT_STATISTICS_CALL(
            statistics().got_representation_equational(der->level(), response.equational.size())
        );
        return response;
    }
};


} // namespace cell_heuristics

} // namespace representation