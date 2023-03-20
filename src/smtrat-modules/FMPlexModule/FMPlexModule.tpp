/**
 * @file FMPlexModule.tpp
 * @author valentin promies
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */
#pragma once

#include "FMPlexModule.h"

namespace smtrat {

template<class Settings>
FMPlexModule<Settings>::FMPlexModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
	Module( _formula, _conditionals, _manager )
{}

template<class Settings>
FMPlexModule<Settings>::~FMPlexModule()
{}

template<class Settings>
bool FMPlexModule<Settings>::informCore( const FormulaT& _constraint ) {
	if (_constraint.type() != carl::FormulaType::CONSTRAINT) {
		return true;
	}

	for (const auto& v : _constraint.variables()) {
		auto it = m_variable_index.lower_bound(v);
		if ((it == m_variable_index.end()) || (it->first != v)) {
			m_variable_index.emplace_hint(it, v, m_variable_index.size());
			m_variable_order.emplace_hint(m_variable_order.end(), m_variables.size(), v);
			m_variables.insert(v);
		}
	}
	return _constraint.constraint().is_consistent() != 0;
}

template<class Settings>
void FMPlexModule<Settings>::init() {}

template<class Settings>
void FMPlexModule<Settings>::add_relation(carl::Relation r) {
	switch (r) {
	case carl::Relation::LESS:
	case carl::Relation::GREATER:
		m_strict_origins.insert(m_constraints.size()-1);
		break;
	case carl::Relation::NEQ:
		m_disequalities.emplace_hint(m_disequalities.end(), m_constraints.size()-1);
		break;
	case carl::Relation::EQ:
		m_equalities.emplace_hint(m_equalities.end(), m_constraints.size()-1);
		break;
	default:
		break;
	}
}

template<class Settings>
bool FMPlexModule<Settings>::addCore( ModuleInput::const_iterator _subformula ) {
	carl::FormulaType type = _subformula->formula().type();

	if (type == carl::FormulaType::TRUE) {
		return true;
	}
	if (type == carl::FormulaType::FALSE) {
		FormulaSetT inf_subset;
		inf_subset.insert(_subformula->formula());
		mInfeasibleSubsets.push_back(inf_subset);
		return false;
	}
	if (type != carl::FormulaType::CONSTRAINT) {
		SMTRAT_LOG_DEBUG("smtrat.fmplex", "trying to add unsupported formula type " << type);
		assert(false);
		return true;
	}
	if (!(_subformula->formula().constraint().lhs().is_linear())) {
		addSubformulaToPassedFormula(_subformula->formula(), _subformula->formula());
		m_non_linear_constraints.insert(_subformula->formula());
		return true;
	}

	m_constraints.push_back(_subformula->formula());
	m_added_constraints.push_back(_subformula->formula());

	add_relation(_subformula->formula().constraint().relation());
	
	return true;
}

template<class Settings>
void FMPlexModule<Settings>::removeCore( ModuleInput::const_iterator _subformula ) {
	if (_subformula->formula().type() != carl::FormulaType::CONSTRAINT) {
		assert(/* unreachable*/false);
	}

	auto it = std::find(m_constraints.begin(), m_constraints.end(), _subformula->formula());
	if (it == m_constraints.end()) return;
	m_constraints.erase(it);

	std::size_t index = std::distance(m_constraints.begin(),it);
	std::set<std::size_t> new_diseqs;
	for (const auto i : m_disequalities) {
		if (i == index) continue;
		if (i > index) new_diseqs.emplace(i-1);
		else new_diseqs.emplace(i);
	}
	m_disequalities = new_diseqs;
	std::set<std::size_t> new_eqs;
	for (const auto i : m_equalities) {
		if (i == index) continue;
		if (i > index) new_eqs.emplace(i-1);
		else new_eqs.emplace(i);
	}
	m_equalities = new_eqs;

}

template<class Settings>
Rational FMPlexModule<Settings>::find_suitable_delta(std::map<std::size_t, fmplex::DeltaRational> working_model) const {
	std::map<carl::Variable, Rational> rational_substitutions;
	std::map<carl::Variable, Rational> delta_substitutions;
	for (const auto& [key, val] : working_model) {
		rational_substitutions.emplace(m_variable_order.at(key), val.mainPart());
		delta_substitutions.emplace(m_variable_order.at(key), val.deltaPart());
	}

	Rational evaluated_poly_main, evaluated_poly_delta;
	Rational current_bound, strictest_bound(1);

	for (const auto& c : m_constraints) {
		carl::Relation r = c.constraint().relation();
		if (r == carl::Relation::EQ) continue;
		bool leq_or_less = (r == carl::Relation::LEQ) || (r == carl::Relation::LESS);

		// we can evaluate separately because the constraints are >>linear<<
		evaluated_poly_main = carl::evaluate(c.constraint().lhs(), rational_substitutions);
		evaluated_poly_delta = carl::evaluate(c.constraint().lhs(), delta_substitutions);
		evaluated_poly_delta -= c.constraint().lhs().constant_part();

		if (carl::is_zero(evaluated_poly_delta)) continue;
		current_bound = (-evaluated_poly_main)/evaluated_poly_delta;

		if (r == carl::Relation::NEQ) {
			if (current_bound <= 0) continue;
		} else if (leq_or_less != (evaluated_poly_delta > 0)) {
			continue; // would give lower bound
		}
		SMTRAT_LOG_DEBUG("smtrat.fmplex", "constraint " << c << " gives bound " << current_bound << " on delta");
		if (current_bound < strictest_bound) strictest_bound = current_bound;
	}

	return carl::sample(RationalInterval(0, strictest_bound), false);
}


template<class Settings>
bool FMPlexModule<Settings>::try_construct_model() {
	SMTRAT_LOG_DEBUG("smtrat.fmplex", "starting model construction...");

	mModel.clear();
	std::map<std::size_t, fmplex::DeltaRational> working_model;
	// use i-1, beginning with current_level - 1 as the current (SAT) level should not contain any variables
	for (std::size_t i = m_current_level; i > 0; i--) {
		m_history[i-1].assign_eliminated_variables<Settings::model_heuristic>(working_model);
	}

	SMTRAT_LOG_DEBUG("smtrat.fmplex", "assigning variables with equalities");
	if constexpr (Settings::eq_handling == fmplex::EQHandling::GAUSSIAN_TABLEAU) {
		m_gauss.assign_variables(working_model);
	} // else: EQHandling & assignment are already done in the Levels

	Rational delta_value = find_suitable_delta(working_model);
	SMTRAT_LOG_DEBUG("smtrat.fmplex", "value for delta: " << delta_value);

	for (const auto& [var, val] : working_model) {
		mModel.emplace(m_variable_order[var], val.mainPart() + (val.deltaPart() * delta_value));
	}

	if constexpr (Settings::neq_handling == fmplex::NEQHandling::SPLITTING_LEMMAS) {
		SMTRAT_LOG_DEBUG("smtrat.fmplex", "handling neqs");
		return handle_neqs();
	} else {
		// todo: not yet implemented
		assert(false);
		return true;
	}
}

template<class Settings>
void FMPlexModule<Settings>::updateModel() const {
	// NOTE: already constructed by try_construct_model which has been called whenever SAT is returned
}

template<class Settings>
void FMPlexModule<Settings>::build_unsat_core(const std::set<std::size_t>& reason) {
	SMTRAT_LOG_DEBUG("smtrat.fmplex", "building unsat core from " << reason);
	FormulaSetT inf_subset;
	for (const std::size_t i : reason) {
		inf_subset.insert(m_constraints[i]);
		SMTRAT_LOG_DEBUG("smtrat.fmplex", i << " -> " << m_constraints[i]);
	}
	mInfeasibleSubsets.push_back(inf_subset);
	SMTRAT_STATISTICS_CALL(m_statistics.conflict_size(inf_subset.size()));
}

template<class Settings>
void FMPlexModule<Settings>::set_level(std::size_t index, const fmplex::Level& level) {
	if (m_history.size() <= index) m_history.push_back(level);
	else m_history[index] = level;
}

template<class Settings>
std::vector<fmplex::Conflict> FMPlexModule<Settings>::construct_root_level() {
	SMTRAT_LOG_DEBUG("smtrat.fmplex", "starting root level construction...");
	m_history.clear();

	// todo: Other NEQHandling might require more case distinctions
	fmplex::FMPlexTableau root_tableau;
	if constexpr (Settings::eq_handling == fmplex::EQHandling::GAUSSIAN_TABLEAU) {
		m_gauss.init(m_constraints, m_variable_index);
		if (m_equalities.size() > 0) {
			SMTRAT_LOG_DEBUG("smtrat.fmplex", "Applying Gaussian elimination");
			SMTRAT_STATISTICS_CALL(m_statistics.gauss_needed());
			m_gauss.apply_gaussian_elimination();
			std::vector<fmplex::Conflict> conflicts = m_gauss.find_all_conflicts();
			if (!conflicts.empty()) return conflicts;
		}
		root_tableau = m_gauss.get_transformed_inequalities();
	} else { // EQHandling is done in Level, along with inequalities
		root_tableau = fmplex::FMPlexTableau(m_constraints, m_variable_index);
	}
	SMTRAT_LOG_DEBUG("smtrat.fmplex", "emplace root level:\n" << root_tableau);
	std::vector<std::size_t> eliminable_columns = root_tableau.non_zero_variable_columns();
	m_history.reserve(eliminable_columns.size() + 1);

	set_level(0, fmplex::Level(root_tableau));

	m_current_level = 0;
	return {};
}

template<class Settings>
bool FMPlexModule<Settings>::backtrack(const fmplex::Conflict& conflict) {
	assert(!conflict.is_global);
	assert(conflict.level > 0);
	if constexpr (Settings::use_backtracking || Settings::ignore_pivots) {
		m_history[conflict.level-1].add_to_unsat_core(conflict.involved_rows);
	}
	m_current_level = conflict.level-1;
	while(m_history[m_current_level].finished()) {
		SMTRAT_LOG_DEBUG("smtrat.fmplex", "level " << m_current_level << " is finished, move up one more step");
		if constexpr (Settings::use_backtracking || Settings::ignore_pivots) {
			if (m_current_level == 0) {
				build_unsat_core(m_history[m_current_level].unsat_core());
				return false;
			}
			m_history[m_current_level-1].add_to_unsat_core(m_history[m_current_level].unsat_core());
		}
		m_current_level--;
	}
	return true;
}

template<class Settings>
bool FMPlexModule<Settings>::handle_neqs() {
	SMTRAT_LOG_DEBUG("smtrat.fmplex", "checking neqs");

	std::size_t nr_splits = 0;
	for (const auto& n : m_disequalities) {
		unsigned consistency = carl::satisfied_by(m_constraints[n], mModel);
		if (consistency == 0) {
			SMTRAT_LOG_DEBUG("smtrat.fmplex", "neq constraint " << m_constraints[n] << " is falsified by model");
			splitUnequalConstraint(m_constraints[n]);
			nr_splits++;
			if (nr_splits >= Settings::nr_neq_splits_at_once) break;
		}
	}
	SMTRAT_STATISTICS_CALL(m_statistics.neq_splits(nr_splits));
	return (nr_splits == 0);
}

template<class Settings>
bool FMPlexModule<Settings>::process_conflict(fmplex::Conflict conflict) {
	if (conflict.is_global){ 						// global conflict => return unsat
		SMTRAT_LOG_DEBUG("smtrat.fmplex", "global conflict! returning UNSAT");
		SMTRAT_STATISTICS_CALL(m_statistics.global_conflict());
		build_unsat_core(conflict.involved_rows);
		return false;
	}
	SMTRAT_LOG_DEBUG("smtrat.fmplex", "local conflict!");
	if constexpr (Settings::use_backtracking) { 	// local conflict => backtrack
		SMTRAT_STATISTICS_CALL(m_statistics.local_conflict(m_current_level - conflict.level + 1));
		SMTRAT_LOG_DEBUG("smtrat.fmplex", "Backtracking...");
		return backtrack(conflict);
	}
	if (m_history[m_current_level].is_lhs_zero()) {
		SMTRAT_LOG_DEBUG("smtrat.fmplex", "in leaf, backtracking one step");
		SMTRAT_STATISTICS_CALL(m_statistics.local_conflict(1));
		conflict.level = m_current_level;
		return backtrack(conflict);
	}
	SMTRAT_LOG_DEBUG("smtrat.fmplex", "but we ignore it.");
	return true;
}

template<class Settings>
Answer FMPlexModule<Settings>::checkCore() {
	SMTRAT_TIME_START(start);

	if (solverState() == Answer::SAT) { // check whether found model still works by chance
		bool all_sat = true;
		for (const auto& c : m_added_constraints) {
			if (carl::satisfied_by(c, mModel) != 1) {
				all_sat = false;
				break;
			}
		}
		if (all_sat) {
			m_added_constraints.clear();
			SMTRAT_LOG_DEBUG("smtrat.fmplex", "last model still satisfies all given constraints");
			SMTRAT_TIME_FINISH(m_statistics.timer(), start);
			SMTRAT_VALIDATION_ADD("smtrat.modules.fmplex","sat_input",FormulaT( carl::FormulaType::AND, m_constraints ), true);
			return Answer::SAT;
		}
	}

	m_added_constraints.clear();
	auto conflicts = construct_root_level();
	if (!conflicts.empty()) {
		SMTRAT_LOG_DEBUG("smtrat.fmplex", "root level is conflicting");
		SMTRAT_STATISTICS_CALL(m_statistics.gauss_conflict());
		for (const auto& conflict : conflicts) {
			build_unsat_core(conflict.involved_rows);
		}
		SMTRAT_TIME_FINISH(m_statistics.timer(), start);
		SMTRAT_VALIDATION_ADD("smtrat.modules.fmplex","unsat_input",FormulaT( carl::FormulaType::AND, m_constraints ), false);
		SMTRAT_STATISTICS_CALL(m_statistics.unsat());
		return Answer::UNSAT;
	}

	while(true) {
		std::optional<fmplex::Conflict> conflict = m_history[m_current_level].earliest_conflict(m_equalities);
		if (conflict) {
			SMTRAT_LOG_DEBUG("smtrat.fmplex", "current level is conflicting");
			if (!process_conflict(*conflict)) {
				SMTRAT_VALIDATION_ADD("smtrat.modules.fmplex","unsat_input",FormulaT( carl::FormulaType::AND, m_constraints ), false);
				SMTRAT_STATISTICS_CALL(m_statistics.unsat());
				return Answer::UNSAT;
			}
		} else if (m_history[m_current_level].is_lhs_zero()) {
			SMTRAT_LOG_DEBUG("smtrat.fmplex", "current level is trivial SAT (apart from NEQs)");
			if constexpr (Settings::neq_handling == fmplex::NEQHandling::SPLITTING_LEMMAS) {
				if (!try_construct_model()) {
					SMTRAT_TIME_FINISH(m_statistics.timer(), start);
					return Answer::UNKNOWN;
				}
			} // todo: else
			SMTRAT_TIME_FINISH(m_statistics.timer(), start);
			SMTRAT_VALIDATION_ADD("smtrat.modules.fmplex","sat_input",FormulaT( carl::FormulaType::AND, m_constraints ), true);
			return Answer::SAT;
		}

		if (!m_history[m_current_level].has_elimination_column()) {
			SMTRAT_LOG_DEBUG("smtrat.fmplex", "choosing elimination column...");
			bool column_found = m_history[m_current_level].choose_elimination_column<Settings::ignore_pivots, Settings::variable_heuristic, Settings::eliminator_heuristic>();
			if constexpr (Settings::ignore_pivots) {
				if (!column_found) { // only happens when all bounds of one type in a column are ignored => partial UNSAT
					SMTRAT_LOG_DEBUG("smtrat.fmplex", "ignored column found -> partial UNSAT");
					SMTRAT_STATISTICS_CALL(m_statistics.local_conflict_from_prune());
					// we don't need to transfer unsat cores, as the reason for partial unsat are already visited sibling or uncle systems
					if (!backtrack(fmplex::Conflict{false, m_current_level, std::set<std::size_t>()})) {
						SMTRAT_TIME_FINISH(m_statistics.timer(), start);
						SMTRAT_VALIDATION_ADD("smtrat.modules.fmplex","unsat_input",FormulaT( carl::FormulaType::AND, m_constraints ), false);
						SMTRAT_STATISTICS_CALL(m_statistics.unsat());
						return Answer::UNSAT;
					}
				}
			}
		}

		set_level(m_current_level + 1, m_history[m_current_level].next_child<Settings::use_backtracking, Settings::ignore_pivots>());
		m_current_level++;
		SMTRAT_STATISTICS_CALL(m_statistics.new_system(m_current_level));
	}

	assert(/* unreachable*/ false);
	return Answer::UNKNOWN;
}

} // namespace smtrat
