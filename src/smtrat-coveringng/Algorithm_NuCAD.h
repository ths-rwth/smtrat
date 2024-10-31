#include "Algorithm.h"

namespace smtrat::covering_ng {

// TODO parameter

template<typename op, typename cell_heuristic>
inline std::optional<std::pair<std::optional<Interval<typename op::PropertiesSet>>, std::vector<cadcells::datastructures::SymbolicInterval>>> nucad_construct_cell(cadcells::datastructures::Projections& proj, std::size_t down_to_level, Interval<typename op::PropertiesSet>& interval) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", down_to_level << ", " << interval->sample());

	std::optional<Interval<typename op::PropertiesSet>> resint = interval;
	std::vector<cadcells::datastructures::SymbolicInterval> sis;
	std::size_t level = (*resint)->level();
	while(level > down_to_level) {
		if (level == 1) {
			auto representation = cell_heuristic::compute(*resint);
			sis.push_back(representation.description);
			resint = std::nullopt;
		} else {
			auto res = characterize_interval<op, cell_heuristic>(*resint);
			if (!res) {
				return std::nullopt;
			} else {
				resint = res->first;
				sis.push_back(res->second.description);
			}
		}
		level--;
	}
	std::reverse(sis.begin(),sis.end());
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got cell " << sis);

	return std::make_pair(resint, sis);
}

inline std::vector<cadcells::RAN> nucad_sample_inside(cadcells::datastructures::Projections& proj, cadcells::Assignment ass, const std::vector<cadcells::datastructures::SymbolicInterval>& cell) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", ass << ", " << cell);

	std::vector<cadcells::RAN> result;
	for (const auto& si : cell) {
		if (si.is_section()) {
			result.emplace_back(proj.evaluate(ass,si.lower().value()).first);
		} else if (!si.lower().is_infty() && !si.upper().is_infty()) {
			assert(proj.evaluate(ass,si.lower().value()).first<proj.evaluate(ass,si.upper().value()).first);
			result.emplace_back(carl::sample_between(proj.evaluate(ass,si.lower().value()).first,proj.evaluate(ass,si.upper().value()).first));
		} else if (!si.upper().is_infty()) {
			assert(si.lower().is_infty());
			result.emplace_back(carl::sample_below(proj.evaluate(ass,si.upper().value()).first));
		}  else if (!si.lower().is_infty()) {
			assert(si.upper().is_infty());
			result.emplace_back(carl::sample_above(proj.evaluate(ass,si.lower().value()).first));
		} else {
			assert(si.lower().is_infty() && si.upper().is_infty());
			result.emplace_back(0);
		}
		ass.emplace(first_unassigned_var(ass,proj.polys().var_order()), result.back());
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got sample " << ass);
	}
	return result;
}

template<typename op, typename FE, typename cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> nucad_quantifier(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification, bool characterize_sat, bool characterize_unsat);


template<typename op, typename FE, typename cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> nucad_recurse(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification, const std::vector<cadcells::RAN>& sample, bool characterize_sat = false, bool characterize_unsat = false) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);

	auto variable = first_unassigned_var(ass, proj.polys().var_order());

	auto initial_ass_size = ass.size();
	for (std::size_t i = 0; i < sample.size(); i++) {
		ass.emplace(proj.polys().var_order()[initial_ass_size+i], sample[i]);
		SMTRAT_STATISTICS_CALL(statistics().formula_evaluation_start());
		f.extend_valuation(ass);
		SMTRAT_STATISTICS_CALL(statistics().formula_evaluation_end());
		assert(f.root_valuation() != formula::Valuation::UNKNOWN);
	}

	CoveringResult<typename op::PropertiesSet> res;
	if (is_full_sample(ass, proj.polys().var_order()) && f.root_valuation() == formula::Valuation::MULTIVARIATE) {
		SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incomplete propagation");
		res =  CoveringResult<typename op::PropertiesSet>();
	} else {
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got evaluation: " << f.root_valuation());
		if (f.root_valuation() == formula::Valuation::FALSE || f.root_valuation() == formula::Valuation::TRUE) {
			auto new_intervals = get_enclosing_intervals<op, FE>(proj, f, ass);
			if (new_intervals.size() > 0) {
				res = CoveringResult<typename op::PropertiesSet>(f.root_valuation() == formula::Valuation::TRUE ? Status::SAT : Status::UNSAT, new_intervals);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Failed due to incomplete projection");
				res = CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
			}
		} else {
			assert(f.root_valuation() == formula::Valuation::MULTIVARIATE);
			assert(!is_full_sample(ass, proj.polys().var_order()));

			std::size_t num_next_levels=0;
			while (ass.size()+num_next_levels < proj.polys().var_order().size() && quantification.var_type(proj.polys().var_order()[ass.size()]) == quantification.var_type(proj.polys().var_order()[ass.size()+num_next_levels])) num_next_levels++;

			const auto variable = first_unassigned_var(ass, proj.polys().var_order());
			auto quantificationType = quantification.var_type(variable);

			if (quantificationType == carl::Quantifier::FREE) {
				quantificationType = carl::Quantifier::EXISTS;
			}

			std::vector<cadcells::datastructures::SymbolicInterval> cell;
			for (std::size_t i=0; i<num_next_levels; i++) cell.emplace_back();

			res = nucad_quantifier<op, FE, cell_heuristic>(proj, f, ass, quantification, quantificationType, cell, characterize_sat, characterize_unsat);
		}
	}

	for (std::size_t i = 0; i < sample.size(); i++) {
		ass.erase(proj.polys().var_order()[initial_ass_size+sample.size()-i-1]);
		f.revert_valuation(ass);
		assert(f.root_valuation() != formula::Valuation::UNKNOWN);
	}
	assert(ass.size() == initial_ass_size);

	return res;
}

template<typename op, typename FE, typename cell_heuristic>
inline CoveringResult<typename op::PropertiesSet> nucad_quantifier(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification, carl::Quantifier next_quantifier, const std::vector<cadcells::datastructures::SymbolicInterval>& cell, bool characterize_sat, bool characterize_unsat) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass);

	auto sample = nucad_sample_inside(proj, ass, cell);
	auto res = nucad_recurse<op,FE,cell_heuristic>(proj, f, ass, quantification, sample, characterize_sat || (next_quantifier == carl::Quantifier::FORALL), characterize_unsat || (next_quantifier == carl::Quantifier::EXISTS));
	if (res.is_failed()) {
		return CoveringResult<typename op::PropertiesSet>(res.status);
	} else if ((res.is_sat() && next_quantifier == carl::Quantifier::EXISTS) || (res.is_unsat() && next_quantifier == carl::Quantifier::FORALL)) {
		if ((res.is_sat() && !characterize_sat) || (res.is_unsat() && !characterize_unsat)) {
			return CoveringResult<typename op::PropertiesSet>(res.status, (*res.intervals().begin())->sample());
		}

		auto input = *res.intervals().begin();
		auto inner_cell = nucad_construct_cell<op,cell_heuristic>(proj, ass.size(), input);
		if (inner_cell) {
			if (inner_cell->first) {
				std::vector<Interval<typename op::PropertiesSet>> new_intervals;
				new_intervals.push_back(*inner_cell->first);
				return CoveringResult<typename op::PropertiesSet>(res.status, new_intervals);
			} else {
				return CoveringResult<typename op::PropertiesSet>(res.status);
			}
		} else {
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Failed due to incomplete projection");
			return CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
		}		
	}

	auto input = *res.intervals().begin();
	for (const auto& si : cell) {
		for (const auto poly : si.polys()) {
			input->insert(cadcells::operators::properties::poly_sgn_inv{poly});
		}
	}
	if (!op::project_basic_properties(*input)) assert(false);
    op::delineate_properties(*input);
    input->delineate_cell();

	auto inner_cell = nucad_construct_cell<op,cell_heuristic>(proj, ass.size(), input);
	if (!inner_cell) {
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Failed due to incomplete projection");
		return CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
	}	
	auto underlying_cell = inner_cell->first;

	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Split " << cell << " using " << inner_cell);
	std::vector<std::vector<cadcells::datastructures::SymbolicInterval>> other_cells;
	std::vector<std::vector<cadcells::datastructures::SymbolicInterval>> other_cells_sections;
	auto tmpass = ass;
	for(std::size_t j=0;j<inner_cell->second.size();j++) {
		tmpass.emplace( first_unassigned_var(tmpass, proj.polys().var_order()), sample[j] );
		if (inner_cell->second.at(j).lower() != cell.at(j).lower() && (cell.at(j).lower().is_infty() || proj.evaluate(tmpass, cell.at(j).lower().value()).first != proj.evaluate(tmpass, inner_cell->second.at(j).lower().value()).first)) {
			assert(cell.at(j).lower().is_infty() || (!inner_cell->second.at(j).lower().is_infty() && proj.evaluate(tmpass, cell.at(j).lower().value()).first < proj.evaluate(tmpass, inner_cell->second.at(j).lower().value()).first));

			other_cells.emplace_back();
			for (std::size_t i=0; i<j;i++) other_cells.back().emplace_back(inner_cell->second.at(i));
			if (inner_cell->second.at(j).lower().is_infty()) {
				other_cells.back().emplace_back(cell.at(j).lower(), cadcells::datastructures::Bound::infty());
			} else {
				other_cells.back().emplace_back(cell.at(j).lower(), cadcells::datastructures::Bound::strict(inner_cell->second.at(j).lower().value()));
			}
			for (std::size_t i=j+1; i<cell.size();i++) other_cells.back().emplace_back(cell.at(i));

			if (!inner_cell->second.at(j).is_section()) {
				other_cells_sections.emplace_back();
				for (std::size_t i=0; i<j;i++) other_cells_sections.back().emplace_back(inner_cell->second.at(i));
				other_cells_sections.back().emplace_back(cadcells::datastructures::Bound::weak(inner_cell->second.at(j).lower().value()),cadcells::datastructures::Bound::weak(inner_cell->second.at(j).lower().value()));
				for (std::size_t i=j+1; i<cell.size();i++) other_cells_sections.back().emplace_back(cell.at(i));
			}
		}

		if (inner_cell->second.at(j).upper() != cell.at(j).upper() && (cell.at(j).upper().is_infty() || proj.evaluate(tmpass, cell.at(j).upper().value()).first != proj.evaluate(tmpass, inner_cell->second.at(j).upper().value()).first)) {
			assert(cell.at(j).upper().is_infty() || (!inner_cell->second.at(j).upper().is_infty() && proj.evaluate(tmpass, cell.at(j).upper().value()).first > proj.evaluate(tmpass, inner_cell->second.at(j).upper().value()).first));

			other_cells.emplace_back();
			for (std::size_t i=0; i<j;i++) other_cells.back().emplace_back(inner_cell->second.at(i));
			if (inner_cell->second.at(j).upper().is_infty()) {
				other_cells.back().emplace_back(cadcells::datastructures::Bound::infty(),cell.at(j).upper());
			} else {
				other_cells.back().emplace_back(cadcells::datastructures::Bound::strict(inner_cell->second.at(j).upper().value()),cell.at(j).upper());
			}
			for (std::size_t i=j+1; i<cell.size();i++) other_cells.back().emplace_back(cell.at(i));

			if (!inner_cell->second.at(j).is_section()) {
				other_cells_sections.emplace_back();
				for (std::size_t i=0; i<j;i++) other_cells_sections.back().emplace_back(inner_cell->second.at(i));
				other_cells_sections.back().emplace_back(cadcells::datastructures::Bound::weak(inner_cell->second.at(j).upper().value()),cadcells::datastructures::Bound::weak(inner_cell->second.at(j).upper().value()));
				for (std::size_t i=j+1; i<cell.size();i++) other_cells_sections.back().emplace_back(cell.at(i));
			}
		}
	}
	other_cells.insert(other_cells.end(), other_cells_sections.begin(), other_cells_sections.end());
	other_cells_sections.clear();
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got cells " << other_cells);

	for (const auto& other_cell : other_cells) {
		auto res = nucad_quantifier<op,FE,cell_heuristic>(proj, f, ass, quantification, next_quantifier, other_cell, characterize_sat, characterize_unsat);
		if (res.is_failed()) {
			return CoveringResult<typename op::PropertiesSet>(res.status);
		} else if ((res.is_sat() && next_quantifier == carl::Quantifier::EXISTS) || (res.is_unsat() && next_quantifier == carl::Quantifier::FORALL)) {
			return res;
		} else {
			if (underlying_cell) {
				(*underlying_cell)->merge_with(**res.intervals().begin());
			}
		}
	}

	if (underlying_cell) {
		std::vector<Interval<typename op::PropertiesSet>> new_intervals;
		new_intervals.push_back(*underlying_cell);
		return CoveringResult<typename op::PropertiesSet>(next_quantifier == carl::Quantifier::EXISTS ? Status::UNSAT : Status::SAT, new_intervals);
	} else {
		return CoveringResult<typename op::PropertiesSet>(next_quantifier == carl::Quantifier::EXISTS ? Status::UNSAT : Status::SAT);
	}
}



}