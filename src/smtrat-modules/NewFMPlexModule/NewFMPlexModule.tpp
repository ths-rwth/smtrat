/**
 * @file NewFMPlex.tpp
 * @author valentin promies
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */
#pragma once

#include "NewFMPlexModule.h"
#include "gauss/Gauss.h"

namespace smtrat {

template<class Settings>
NewFMPlexModule<Settings>::NewFMPlexModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
	Module( _formula, _conditionals, _manager ), m_initial_tableau(0,0) // REVIEW: this is hacky
{}

template<class Settings>
NewFMPlexModule<Settings>::~NewFMPlexModule()
{}

template<class Settings>
bool NewFMPlexModule<Settings>::informCore( const FormulaT& _constraint ) {
	if (_constraint.type() == carl::FormulaType::CONSTRAINT) {
		for (const auto& v : _constraint.variables()) {
			if (m_variable_index.find(v) == m_variable_index.end()) {
				m_variable_index.emplace(v, m_variable_index.size());
				m_variable_order.emplace_hint(m_variable_order.end(), m_variables.size(), v);
				m_variables.insert(v);
			}
		}
		return _constraint.constraint().is_consistent() != 0;
	}
	return true;
}

template<class Settings>
void NewFMPlexModule<Settings>::init() {}

template<class Settings>
bool NewFMPlexModule<Settings>::addCore( ModuleInput::const_iterator _subformula ) {
	switch (_subformula->formula().type()){
		case carl::FormulaType::TRUE: return true;
		case carl::FormulaType::FALSE: {
			FormulaSetT inf_subset;
			inf_subset.insert(_subformula->formula());
			mInfeasibleSubsets.push_back(inf_subset);
			return false;
		}
		case carl::FormulaType::CONSTRAINT: {
			if (_subformula->formula().constraint().lhs().is_linear()) {
				// todo: other eq/neq handling NOTE: this works only for GAUSSIAN_TABLEAU and SPLITTING_LEMMAS
				m_constraints.push_back(_subformula->formula());
				if constexpr (Settings::incremental) {
					m_added_constraints.push_back(_subformula->formula());
					// todo: not yet implemented
				}
				carl::Relation r = _subformula->formula().constraint().relation();
				if ((r == carl::Relation::LESS) || (r == carl::Relation::GREATER)) {
					m_strict_origins.insert(m_constraints.size()-1);
				} else if (r == carl::Relation::NEQ) m_neqs.push_back(_subformula->formula());
			} else { // constraint is non-linear
				addSubformulaToPassedFormula(_subformula->formula(), _subformula->formula());
				m_non_linear_constraints.insert(_subformula->formula());
			}
			return true;	
		}
		default:
			assert(false); // unsupported
			return true;
	}
}

template<class Settings>
void NewFMPlexModule<Settings>::removeCore( ModuleInput::const_iterator _subformula ) {
	if (_subformula->formula().type() != carl::FormulaType::CONSTRAINT) {
		assert(false); // unreachable?
	} else {
		auto it = std::find(m_constraints.begin(), m_constraints.end(), _subformula->formula());
		if (it != m_constraints.end()) m_constraints.erase(it);
		if (_subformula->formula().constraint().relation() == carl::Relation::NEQ) {
			auto it = std::find(m_neqs.begin(), m_neqs.end(), _subformula->formula());
			if (it != m_neqs.end()) m_neqs.erase(it);
		}
	}
	// todo: other eq/neq handling NOTE: this works only for GAUSSIAN_TABLEAU and SPLITTING_LEMMAS
	// todo: Incrementality
}

template<class Settings>
bool NewFMPlexModule<Settings>::try_construct_model() {
	// todo: incrementality?
	mModel.clear();
	std::map<std::size_t, fmplex::DeltaRational> working_model;
	Rational strictest_delta_bound(1);
	// use i-1, beginning with current_level - 1 as the current (SAT) level should not contain any variables
	for (std::size_t i = m_current_level; i > 0; i--) {
		std::optional<Rational> delta_bound = m_history[i-1].assign_eliminated_variables(working_model);
		if (delta_bound && ((*delta_bound) < strictest_delta_bound)) strictest_delta_bound = *delta_bound;
	}

	// TODO: NEQ handling here
	
	if constexpr (Settings::eq_handling == EQHandling::GAUSSIAN_TABLEAU) {
		if (!m_gauss_order.empty()) {
			for (std::size_t i = m_gauss_order.size() - 1; i >= 0; i--) {
				auto [row, col] = m_gauss_order[i];
				std::vector<std::size_t> cols = m_initial_tableau.non_zero_variable_columns(row);
				for (const std::size_t j : cols) {
					if (!((j == col) || (working_model.count(j) == 1))) {
						// assign 0 to implicitly eliminated variables todo: do this once for the whole tableau instead of in this loop
						working_model.emplace(j,0);
					}
				}
				fmplex::DeltaRational v = m_initial_tableau.bound_value(row, col, working_model);
				working_model.emplace(col,v);
			}
		}
	} else {
		// todo: not yet implemented
		assert(false);
	}

	Rational appropriate_delta = carl::sample(RationalInterval(0,strictest_delta_bound),false);
	std::cout << "delta: " << appropriate_delta;
	for (const auto& [var, val] : working_model) {
		mModel.emplace(m_variable_order[var], val.mainPart() + (val.deltaPart() * appropriate_delta));
	}

	std::cout << "Constructed Model: " << mModel << "\n";

	if constexpr (Settings::neq_handling == NEQHandling::SPLITTING_LEMMAS) {
		return handle_neqs();
	} else {
		// todo: not yet implemented
		assert(false);
		return true;
	}
}

template<class Settings>
void NewFMPlexModule<Settings>::updateModel() const {
	//mModel.clear();
	if( solverState() == Answer::SAT ) {
		// NOTE: already constructed by try_construct_model which should have been called whenever SAT is returned
	}
}

template<class Settings>
void NewFMPlexModule<Settings>::build_unsat_core(const std::set<std::size_t>& reason) {
	FormulaSetT inf_subset;
	for (const std::size_t i : reason) {
		inf_subset.insert(m_constraints[i]);
	}
	mInfeasibleSubsets.push_back(inf_subset);
}

template<class Settings>
std::optional<fmplex::Conflict> NewFMPlexModule<Settings>::construct_root_level() {
	if constexpr (Settings::eq_handling == EQHandling::GAUSSIAN_TABLEAU) {
		m_initial_tableau = fmplex::FMPlexTableau(m_constraints, m_variable_index);
		if (m_equalities.size() > 0) {
			m_initial_tableau.apply_gaussian_elimination();
			for (std::size_t i = 0; i < m_initial_tableau.nr_of_rows(); i++) {
				if (m_initial_tableau.is_row_conflict(i)) {
					return fmplex::Conflict{0, m_initial_tableau.origins(i).first};
				}
			}
		}
		fmplex::FMPlexTableau root_tableau = m_initial_tableau.restrict_to_inequalities(); // TODO: only do this if there are EQS/neqs
		std::vector<std::size_t> eliminatable_columns = root_tableau.non_zero_variable_columns();
		m_history.reserve(eliminatable_columns.size() + 1);
		if (m_history.empty()) m_history.emplace_back(root_tableau);
		else m_history[0] = fmplex::Level(root_tableau);

		m_current_level = 0;
		for (const auto c : eliminatable_columns) {
			m_elimination_variables.emplace_hint(m_elimination_variables.end(), m_variable_order[c]);
		}
	} else {
		// todo: other eq-handling
	}
	return std::nullopt;
}

template<class Settings>
void NewFMPlexModule<Settings>::backtrack(const fmplex::Conflict& conflict) {
	assert(conflict.level > 0);
	m_history[conflict.level-1].add_to_unsat_core(conflict.involved_rows);
	m_current_level = conflict.level-1;
}

template<class Settings>
bool NewFMPlexModule<Settings>::handle_neqs() {
	std::size_t nr_splits = 0;
	for (const auto& n : m_neqs) {
		unsigned consistency = carl::satisfied_by(n, mModel);
		if (consistency == 0) {
			splitUnequalConstraint(n);
			nr_splits++;
			if (nr_splits >= Settings::nr_neq_splits_at_once) break;
		} else if (consistency == 2) {
			// TODO: handle what happens if n contains variables not present in mModel
		}
	}
	return nr_splits == 0;
}

template<class Settings>
Answer NewFMPlexModule<Settings>::checkCore() {
	std::cout << "in checkcore\n";
	// Incrementality
	if constexpr (Settings::incremental) {
		// todo: not yet implemented
	} else {
		auto conflict = construct_root_level();
		if (conflict) {
			build_unsat_core(conflict->involved_rows);
			return Answer::UNSAT;
		}
	}

	std::cout << "variable index: " << m_variable_index << "\n";

	// Main loop
	while(true) {
		std::cout << "in loop\n";
		std::optional<fmplex::Conflict> conflict = m_history[m_current_level].earliest_conflict(m_strict_origins);
		if (conflict) {
			if (conflict->level == 0){ 						// global conflict => return unsat
				build_unsat_core(conflict->involved_rows);
				return Answer::UNSAT;
			}
			if constexpr (Settings::use_backtracking) { 	// local conflict => maybe backtrack
				backtrack(*conflict);
			}
		} else if ((m_current_level == m_max_level) || (m_history[m_current_level].is_lhs_zero())) {
			if constexpr (Settings::neq_handling == NEQHandling::SPLITTING_LEMMAS) {
				if (!try_construct_model()) return Answer::UNKNOWN;
			} // todo: else?
			return Answer::SAT;
		}

		bool column_found = m_history[m_current_level].choose_elimination_column<Settings::ignore_pivots, Settings::variable_heuristic>();
		if constexpr (Settings::ignore_pivots) {
			if (!column_found) { // only happens when all bounds of one type in a column are ignored => partial UNSAT
				m_current_level--;
			}
		}
		std::cout << "after choosevar\n";
		// move back to the most recent level with unchecked eliminators
		while(m_history[m_current_level].finished()) {
			std::cout << "after finished\n";
			if constexpr (Settings::use_backtracking || Settings::ignore_pivots) {
				// If all eliminators of the root level are checked, return UNSAT
				if (m_current_level == 0) {
					build_unsat_core(m_history[m_current_level].unsat_core());
					return Answer::UNSAT;
				}
				m_history[m_current_level-1].add_to_unsat_core(m_history[m_current_level].unsat_core());
			}
			m_current_level--;
		}
		// construct next child, which will be checked in the next iteration
		if (m_history.size() <= m_current_level + 1) m_history.push_back(m_history[m_current_level].next_child());
		else m_history[m_current_level + 1] = m_history[m_current_level].next_child(); // REVIEW: construct inplace with reference parameters?
		m_current_level++;
	}
	assert(false); // unreachable
	return Answer::UNKNOWN;
}

} // namespace smtrat
