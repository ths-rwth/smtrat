#include "Algorithm.h"

#ifdef SMTRAT_DEVOPTION_Validation
#include <smtrat-cadcells/helper_formula.h>
#endif

namespace smtrat::covering_ng {

template<typename op, typename cell_heuristic>
inline std::optional<std::pair<std::optional<Interval<typename op::PropertiesSet>>, std::vector<cadcells::datastructures::SymbolicInterval>>> nucad_construct_cell(std::size_t down_to_level, Interval<typename op::PropertiesSet>& interval) {
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

inline std::optional<std::vector<cadcells::RAN>> nucad_sample_inside(cadcells::datastructures::Projections& proj, cadcells::Assignment ass, const std::vector<cadcells::datastructures::SymbolicInterval>& cell) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", ass << ", " << cell);

	std::vector<cadcells::RAN> result;
	for (const auto& si : cell) {
		if (si.is_section() || (si.lower().is_weak() && si.upper().is_weak() && proj.evaluate(ass,si.lower().value()).first==proj.evaluate(ass,si.upper().value()).first)) {
			result.emplace_back(proj.evaluate(ass,si.lower().value()).first);
		} else if (!si.lower().is_infty() && !si.upper().is_infty()) {
			assert(proj.evaluate(ass,si.lower().value()).first<=proj.evaluate(ass,si.upper().value()).first);
			if (proj.evaluate(ass,si.lower().value()).first==proj.evaluate(ass,si.upper().value()).first) return std::nullopt;
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

template<typename op, typename FE, typename cell_heuristic, bool enable_weak>
inline CoveringResult<typename op::PropertiesSet> nucad_quantifier(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification, bool characterize_sat, bool characterize_unsat);


template<typename op, typename FE, typename cell_heuristic, bool enable_weak>
inline CoveringResult<typename op::PropertiesSet> nucad_recurse(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification, const std::vector<cadcells::RAN>& sample, bool characterize_sat = false, bool characterize_unsat = false) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass << ", " << sample);

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

			std::vector<cadcells::datastructures::SymbolicInterval> cell;
			for (std::size_t i=0; i<num_next_levels; i++) cell.emplace_back();

			auto sres = nucad_quantifier<op, FE, cell_heuristic,enable_weak>(proj, f, ass, quantification, quantification.var_type(variable), cell, characterize_sat, characterize_unsat);
			assert(sres);
			res = *sres;
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

struct NuCADTreeBuilder {
	carl::Variable var = carl::Variable::NO_VARIABLE;
	cadcells::datastructures::SymbolicInterval interval;
	std::optional<ParameterTree> subtree;

	std::shared_ptr<NuCADTreeBuilder> lo;
	std::shared_ptr<NuCADTreeBuilder> lb;
	std::shared_ptr<NuCADTreeBuilder> m;
	std::shared_ptr<NuCADTreeBuilder> ub;
	std::shared_ptr<NuCADTreeBuilder> uo;
};

inline ParameterTree to_parameter_tree(std::shared_ptr<NuCADTreeBuilder> in) {
	std::vector<ParameterTree> children;
	if (in->subtree) {
		children.push_back(*in->subtree);
	} else {
		if (in->lo) children.push_back(to_parameter_tree(in->lo));
		if (in->lb) children.push_back(to_parameter_tree(in->lb));
		if (in->m ) children.push_back(to_parameter_tree(in->m ));
		if (in->ub) children.push_back(to_parameter_tree(in->ub));
		if (in->uo) children.push_back(to_parameter_tree(in->uo));
	}
	if (in->var == carl::Variable::NO_VARIABLE) {
		return ParameterTree(std::move(children)); 
	} else {
		return ParameterTree(in->var, in->interval, carl::Assignment<cadcells::RAN>(), std::move(children)); 
	}
}

template<typename op, typename FE, typename cell_heuristic, bool enable_weak>
inline std::optional<CoveringResult<typename op::PropertiesSet>> nucad_quantifier(cadcells::datastructures::Projections& proj, FE& f, cadcells::Assignment ass, const VariableQuantification& quantification, carl::Quantifier next_quantifier, const std::vector<cadcells::datastructures::SymbolicInterval>& cell, bool characterize_sat, bool characterize_unsat) {
	SMTRAT_LOG_FUNC("smtrat.covering_ng", "f, " << ass << ", " << next_quantifier << ", " << cell);

	auto sample = nucad_sample_inside(proj, ass, cell); // TODO make non-optional again?
	if (!sample) {
		assert(false);
		//assert(enable_weak);
		return std::nullopt;
	}
	auto res = nucad_recurse<op,FE,cell_heuristic,enable_weak>(proj, f, ass, quantification, *sample, characterize_sat || (next_quantifier == carl::Quantifier::FORALL) || (next_quantifier == carl::Quantifier::FREE), characterize_unsat || (next_quantifier == carl::Quantifier::EXISTS) || (next_quantifier == carl::Quantifier::FREE));
	if (res.is_failed()) {
		return CoveringResult<typename op::PropertiesSet>(res.status);
	} else if ((res.is_sat() && next_quantifier == carl::Quantifier::EXISTS) || (res.is_unsat() && next_quantifier == carl::Quantifier::FORALL)) {
		if ((res.is_sat() && !characterize_sat) || (res.is_unsat() && !characterize_unsat)) {
			return CoveringResult<typename op::PropertiesSet>(res.status, (*res.intervals().begin())->sample());
		}

		auto input = *res.intervals().begin();
		auto inner_cell = nucad_construct_cell<op,cell_heuristic>(ass.size(), input);
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
		//for (const auto poly : si.polys()) {
		//	input->insert(cadcells::operators::properties::poly_sgn_inv{poly});
		//}
		if (si.is_section()) {
			input->insert(cadcells::operators::properties::iroot_constraint_truth_inv(cadcells::datastructures::IndexedRootConstraint{carl::Relation::EQ,si.section_defining()}));
		} else {
			if (si.lower().is_weak()) {
				assert(si.lower().value().is_root()); // other cases not implemented
				input->insert(cadcells::operators::properties::iroot_constraint_truth_inv(cadcells::datastructures::IndexedRootConstraint{carl::Relation::GEQ,si.lower().value().root()}));
			} else if (si.lower().is_strict()) {
				assert(si.lower().value().is_root()); // other cases not implemented
				input->insert(cadcells::operators::properties::iroot_constraint_truth_inv(cadcells::datastructures::IndexedRootConstraint{carl::Relation::GREATER,si.lower().value().root()}));
			}
			if (si.upper().is_weak()) {
				assert(si.upper().value().is_root()); // other cases not implemented
				input->insert(cadcells::operators::properties::iroot_constraint_truth_inv(cadcells::datastructures::IndexedRootConstraint{carl::Relation::LEQ,si.upper().value().root()}));
			} else if (si.upper().is_strict()) {
				assert(si.upper().value().is_root()); // other cases not implemented
				input->insert(cadcells::operators::properties::iroot_constraint_truth_inv(cadcells::datastructures::IndexedRootConstraint{carl::Relation::LESS,si.upper().value().root()}));
			}
		}
	}
	if (!op::project_basic_properties(*input)) assert(false);
    op::delineate_properties(*input);
    input->delineate_cell();

	auto inner_cell = nucad_construct_cell<op,cell_heuristic>(ass.size(), input);
	if (!inner_cell) {
		SMTRAT_LOG_TRACE("smtrat.covering_ng", "Failed due to incomplete projection");
		return CoveringResult<typename op::PropertiesSet>(Status::FAILED_PROJECTION);
	}

	#ifdef SMTRAT_DEVOPTION_Validation 
	FormulasT lemma;
	for (std::size_t j=0;j<inner_cell->second.size();j++) {
		auto var = proj.polys().var_order().at(ass.size()+j);
		lemma.emplace_back(smtrat::cadcells::helper::to_formula_carl(proj.polys(), var, inner_cell->second.at(j)));
	}
	FormulasT lemma1;
	for (std::size_t j=0;j<cell.size();j++) {
		auto var = proj.polys().var_order().at(ass.size()+j);
		lemma1.emplace_back(smtrat::cadcells::helper::to_formula_carl(proj.polys(), var, cell.at(j)));
	}
	lemma.emplace_back(FormulaT(carl::FormulaType::AND, std::move(lemma1)).negated());
	SMTRAT_VALIDATION_ADD("smtrat.covering_ng", "nucad_result", FormulaT(carl::FormulaType::AND, std::move(lemma)), false);
	#endif

	auto underlying_cell = inner_cell->first;

	std::shared_ptr<NuCADTreeBuilder> nucad_root;
	if (next_quantifier == carl::Quantifier::FREE) {
		nucad_root = std::make_shared<NuCADTreeBuilder>();
		std::shared_ptr<NuCADTreeBuilder> current = nucad_root;
		auto variter = proj.polys().var_order().begin() + ass.size();
		for (const auto& si : inner_cell->second) {
			current->m = std::make_shared<NuCADTreeBuilder>();
			current = current->m;
			current->var = *variter;
			current->interval = si;
			variter++;
		}
		current->subtree = std::move(res.parameter_tree());
	}
	
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Split " << cell << " using " << inner_cell->second);
	std::vector<std::pair<std::vector<cadcells::datastructures::SymbolicInterval>,std::shared_ptr<NuCADTreeBuilder>>> other_cells;
	std::vector<std::pair<std::vector<cadcells::datastructures::SymbolicInterval>,std::shared_ptr<NuCADTreeBuilder>>> other_cells_sections;
	auto tmpass = ass;
	for(std::size_t j=0;j<inner_cell->second.size();j++) {
		auto current_var = first_unassigned_var(tmpass, proj.polys().var_order());
		tmpass.emplace( current_var, (*sample)[j] );

		// TODO darf man das machen mit replace?
		if (!cell.at(j).lower().is_infty() && proj.evaluate(tmpass, cell.at(j).lower().value()).first == proj.evaluate(tmpass, inner_cell->second.at(j).lower().value()).first) {
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Replace " << inner_cell->second.at(j).lower().value() << " by " <<  cell.at(j).lower().value());
			inner_cell->second[j].lower().set_value(cell.at(j).lower().value());
		}
		if (!cell.at(j).upper().is_infty() && proj.evaluate(tmpass, cell.at(j).upper().value()).first == proj.evaluate(tmpass, inner_cell->second.at(j).upper().value()).first) {
			SMTRAT_LOG_TRACE("smtrat.covering_ng", "Replace " << inner_cell->second.at(j).upper().value() << " by " <<  cell.at(j).upper().value());
			inner_cell->second[j].upper().set_value(cell.at(j).upper().value());
		}

		if (inner_cell->second.at(j).lower() != cell.at(j).lower()) {
			assert(cell.at(j).lower().is_infty() || (!inner_cell->second.at(j).lower().is_infty() && ((proj.evaluate(tmpass, cell.at(j).lower().value()).first == proj.evaluate(tmpass, inner_cell->second.at(j).lower().value()).first && cell.at(j).lower().is_weak() && inner_cell->second.at(j).lower().is_strict()) || (proj.evaluate(tmpass, cell.at(j).lower().value()).first < proj.evaluate(tmpass, inner_cell->second.at(j).lower().value()).first))));
			//assert(cell.at(j).lower().is_infty() || (!inner_cell->second.at(j).lower().is_infty() && ((proj.evaluate(tmpass, cell.at(j).lower().value()).first <= proj.evaluate(tmpass, inner_cell->second.at(j).lower().value()).first))));

			other_cells.emplace_back();
			for (std::size_t i=0; i<j;i++) other_cells.back().first.emplace_back(inner_cell->second.at(i));
			if (inner_cell->second.at(j).lower().is_infty()) {
				other_cells.back().first.emplace_back(cell.at(j).lower(), cadcells::datastructures::Bound::infty());
			} else if (inner_cell->second.at(j).lower().is_strict() && enable_weak) {
				other_cells.back().first.emplace_back(cell.at(j).lower(), cadcells::datastructures::Bound::weak(inner_cell->second.at(j).lower().value()));
			} else {
				other_cells.back().first.emplace_back(cell.at(j).lower(), cadcells::datastructures::Bound::strict(inner_cell->second.at(j).lower().value()));
			}
			for (std::size_t i=j+1; i<cell.size();i++) other_cells.back().first.emplace_back(cell.at(i));

			if (next_quantifier == carl::Quantifier::FREE) {
				std::shared_ptr<NuCADTreeBuilder> current = nucad_root;
				for (std::size_t i=0; i<j;i++) current = current->m;
				current->lo = std::make_shared<NuCADTreeBuilder>();
				current = current->lo;
				current->var = current_var;
				current->interval = other_cells.back().first.at(j);
				other_cells.back().second = current;
			}

			if (inner_cell->second.at(j).lower().is_strict() && ! enable_weak) {
				other_cells_sections.emplace_back();
				for (std::size_t i=0; i<j;i++) other_cells_sections.back().first.emplace_back(inner_cell->second.at(i));
				other_cells_sections.back().first.emplace_back(cadcells::datastructures::Bound::weak(inner_cell->second.at(j).lower().value()),cadcells::datastructures::Bound::weak(inner_cell->second.at(j).lower().value()));
				for (std::size_t i=j+1; i<cell.size();i++) other_cells_sections.back().first.emplace_back(cell.at(i));

				if (next_quantifier == carl::Quantifier::FREE) {
					std::shared_ptr<NuCADTreeBuilder> current = nucad_root;
					for (std::size_t i=0; i<j;i++) current = current->m;
					current->lb = std::make_shared<NuCADTreeBuilder>();
					current = current->lb;
					current->var = current_var;
					current->interval = other_cells_sections.back().first.at(j);
					other_cells_sections.back().second = current;
				}
			}
		}

		if (inner_cell->second.at(j).upper() != cell.at(j).upper()) {
			assert(cell.at(j).upper().is_infty() || (!inner_cell->second.at(j).upper().is_infty() && ((proj.evaluate(tmpass, cell.at(j).upper().value()).first == proj.evaluate(tmpass, inner_cell->second.at(j).upper().value()).first && cell.at(j).upper().is_weak() && inner_cell->second.at(j).upper().is_strict()) || (proj.evaluate(tmpass, cell.at(j).upper().value()).first > proj.evaluate(tmpass, inner_cell->second.at(j).upper().value()).first))));
			//assert(cell.at(j).upper().is_infty() || (!inner_cell->second.at(j).upper().is_infty() && ((proj.evaluate(tmpass, cell.at(j).upper().value()).first >= proj.evaluate(tmpass, inner_cell->second.at(j).upper().value()).first))));

			other_cells.emplace_back();
			for (std::size_t i=0; i<j;i++) other_cells.back().first.emplace_back(inner_cell->second.at(i));
			if (inner_cell->second.at(j).upper().is_infty()) {
				other_cells.back().first.emplace_back(cadcells::datastructures::Bound::infty(),cell.at(j).upper());
			} else if (inner_cell->second.at(j).upper().is_strict() && enable_weak) {
				other_cells.back().first.emplace_back( cadcells::datastructures::Bound::weak(inner_cell->second.at(j).upper().value()), cell.at(j).upper());
			} else {
				other_cells.back().first.emplace_back(cadcells::datastructures::Bound::strict(inner_cell->second.at(j).upper().value()),cell.at(j).upper());
			}
			for (std::size_t i=j+1; i<cell.size();i++) other_cells.back().first.emplace_back(cell.at(i));

			if (next_quantifier == carl::Quantifier::FREE) {
				std::shared_ptr<NuCADTreeBuilder> current = nucad_root;
				for (std::size_t i=0; i<j;i++) current = current->m;
				current->uo = std::make_shared<NuCADTreeBuilder>();
				current = current->uo;
				current->var = current_var;
				current->interval = other_cells.back().first.at(j);
				other_cells.back().second = current;
			}

			if (inner_cell->second.at(j).upper().is_strict() && ! enable_weak) {
				other_cells_sections.emplace_back();
				for (std::size_t i=0; i<j;i++) other_cells_sections.back().first.emplace_back(inner_cell->second.at(i));
				other_cells_sections.back().first.emplace_back(cadcells::datastructures::Bound::weak(inner_cell->second.at(j).upper().value()),cadcells::datastructures::Bound::weak(inner_cell->second.at(j).upper().value()));
				for (std::size_t i=j+1; i<cell.size();i++) other_cells_sections.back().first.emplace_back(cell.at(i));

				if (next_quantifier == carl::Quantifier::FREE) {
					std::shared_ptr<NuCADTreeBuilder> current = nucad_root;
					for (std::size_t i=0; i<j;i++) current = current->m;
					current->ub = std::make_shared<NuCADTreeBuilder>();
					current = current->ub;
					current->var = current_var;
					current->interval = other_cells_sections.back().first.at(j);
					other_cells_sections.back().second = current;
				}
			}
		}
	}
	other_cells.insert(other_cells.end(), other_cells_sections.begin(), other_cells_sections.end());
	other_cells_sections.clear();
	SMTRAT_LOG_TRACE("smtrat.covering_ng", "Got cells " << other_cells);

	for (const auto& other_cell : other_cells) {
		#ifdef SMTRAT_DEVOPTION_Validation 
		FormulasT lemma;
		for (std::size_t j=0;j<other_cell.first.size();j++) {
			auto var = proj.polys().var_order().at(ass.size()+j);
			lemma.emplace_back(smtrat::cadcells::helper::to_formula_carl(proj.polys(), var, other_cell.first.at(j)));
		}
		FormulasT lemma1;
		for (std::size_t j=0;j<cell.size();j++) {
			auto var = proj.polys().var_order().at(ass.size()+j);
			lemma1.emplace_back(smtrat::cadcells::helper::to_formula_carl(proj.polys(), var, cell.at(j)));
		}
		lemma.emplace_back(FormulaT(carl::FormulaType::AND, std::move(lemma1)).negated());
		SMTRAT_VALIDATION_ADD("smtrat.covering_ng", "nucad_split", FormulaT(carl::FormulaType::AND, std::move(lemma)), false);
		#endif

		auto sres = nucad_quantifier<op,FE,cell_heuristic,enable_weak>(proj, f, ass, quantification, next_quantifier, other_cell.first, characterize_sat, characterize_unsat);
		if (!sres) {
			//other_cell.second->subtree = ParameterTree(0);
		} else {
			auto res = *sres;
			if (res.is_failed()) {
				return CoveringResult<typename op::PropertiesSet>(res.status);
			} else if ((res.is_sat() && next_quantifier == carl::Quantifier::EXISTS) || (res.is_unsat() && next_quantifier == carl::Quantifier::FORALL)) {
				return res;
			} else {
				if (underlying_cell) {
					(*underlying_cell)->merge_with(**res.intervals().begin());
				}
				if (next_quantifier == carl::Quantifier::FREE) {
					other_cell.second->subtree = std::move(res.parameter_tree());
				}
			}
		}
	}

	if (underlying_cell) {
		std::vector<Interval<typename op::PropertiesSet>> new_intervals;
		new_intervals.push_back(*underlying_cell);
		if (next_quantifier == carl::Quantifier::FREE) {
			return CoveringResult<typename op::PropertiesSet>(Status::SAT, to_parameter_tree(nucad_root), new_intervals);
		} else {
			return CoveringResult<typename op::PropertiesSet>(next_quantifier == carl::Quantifier::EXISTS ? Status::UNSAT : Status::SAT, new_intervals);
		}
	} else {
		if (next_quantifier == carl::Quantifier::FREE) {
			return CoveringResult<typename op::PropertiesSet>(Status::SAT, to_parameter_tree(nucad_root));
		} else {
			return CoveringResult<typename op::PropertiesSet>(next_quantifier == carl::Quantifier::EXISTS ? Status::UNSAT : Status::SAT);
		}
	}
}



}