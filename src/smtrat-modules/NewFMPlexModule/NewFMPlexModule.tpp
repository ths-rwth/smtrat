/**
 * @file NewFMPlex.cpp
 * @author valentin promies
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */
#pragma once

#include "NewFMPlexModule.h"
#include "Gauss.h"

namespace smtrat {

	template<class Settings>
	NewFMPlexModule<Settings>::NewFMPlexModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
	{}
	
	template<class Settings>
	NewFMPlexModule<Settings>::~NewFMPlexModule()
	{}
	
	template<class Settings>
	bool NewFMPlexModule<Settings>::informCore( const FormulaT& _constraint ) {
		// TODO: check for non-linear?
		// TODO: check for trivially True/false
		for (const auto& v : _constraint.variables()) {
			if (m_variable_index.find(v) == m_variable_index.end()) {
				m_variable_index.emplace(v, m_variable_index.size());
				m_variable_order.emplace_hint(m_variable_order.end(), m_variables.size(), v);
				m_variables.insert(v);
			}
		}
		return true;
	}
	
	template<class Settings>
	void NewFMPlexModule<Settings>::init()
	{}
	
	template<class Settings>
	bool NewFMPlexModule<Settings>::addCore( ModuleInput::const_iterator _subformula ) {
		// TODO: check for non-linear?
		// TODO: check for trivial sat/unsat
		if (_subformula->formula().type() != carl::FormulaType::CONSTRAINT) {
			assert(false); // unreachable?
		} else if (_subformula->formula().constraint().relation() == carl::Relation::NEQ) {
			m_neqs.push_back(_subformula->formula());
		} else {
			m_constraints.push_back(_subformula->formula()); // TODO: check for duplicates?
			if constexpr (Settings::incremental) {
				m_added_constraints.push_back(_subformula->formula());
			}
			// TODO: watch out for incrementality
			if (carl::is_strict(_subformula->formula().constraint().relation())) {
				m_strict_origins.insert(m_constraints.size()-1);
			}
		}
		return true;
	}
	
	template<class Settings>
	void NewFMPlexModule<Settings>::removeCore( ModuleInput::const_iterator _subformula ) {
		if (_subformula->formula().type() != carl::FormulaType::CONSTRAINT) {
			assert(false); // unreachable?
		} else if (_subformula->formula().constraint().relation() == carl::Relation::NEQ) {
			auto it = std::find(m_neqs.begin(), m_neqs.end(), _subformula->formula());
			if (it != m_neqs.end()) m_neqs.erase(it);
		} else {
			auto it = std::find(m_constraints.begin(), m_constraints.end(), _subformula->formula());
			if (it != m_constraints.end()) m_constraints.erase(it);
		}
		
		// TODO: Incrementality
	}
	
	template<class Settings>
	void NewFMPlexModule<Settings>::updateModel() const {
		mModel.clear();
		if( solverState() == Answer::SAT ) {
			for (const auto& v : m_elimination_variables) {
				mModel.emplace(v,0);
			}
			std::map<std::size_t, Rational> working_model;
			for (std::size_t i = m_current_level; i >= 0; i--) {
				Rational v = m_history[i].find_variable_assignment(working_model);
				std::size_t elim_variable_index = m_history[i].eliminated_column_index();
				working_model.emplace(elim_variable_index, v);
				mModel.emplace(m_variable_order.at(elim_variable_index), v);
			}
		}
	}
	
	template<class Settings>
	Answer NewFMPlexModule<Settings>::checkCore() {
		// Incrementality
		if constexpr (Settings::incremental) {
			// TODO: (low priority)
		} else {
			construct_root_level();
		}

		// Main loop
		while(true) {
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
					updateModel(); // TODO: is this appropriate? -> no because of solver state guard
					if (!handle_neqs()) return Answer::UNKNOWN;
				}
				return Answer::SAT;
			}

			// TODO: choose elimination column

			// move back to the most recent level with unchecked eliminators
			while(m_history[m_current_level].finished()) {
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
			m_history[m_current_level + 1] = m_history[m_current_level].next_child(); // TODO: construct inplace with parameter arguments?
			m_current_level++;
		}
		assert(false); // unreachable
		return Answer::UNKNOWN;
	}

	template<class Settings>
	void NewFMPlexModule<Settings>::build_unsat_core(const std::set<std::size_t>& reason) {
		// TODO: take equality handling into account
	}

	template<class Settings>
	void NewFMPlexModule<Settings>::construct_root_level() {
		// TODO: check for redundancies -> in tableau?
		m_history.reserve(m_variables.size());
		m_history[0] = fmplex::FMPlexTableau(m_constraints, m_variable_index);
		if constexpr (Settings::eq_handling == EQHandling::GAUSSIAN) {
			gaussian_elimination();
		}
		m_current_level = 0;
		m_elimination_variables = m_variables; // TODO: retrieve eliminated vars from tableaus
	}

	template<class Settings>
	void NewFMPlexModule<Settings>::gaussian_elimination() {
		// TODO: inputs/outputs?
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
			unsigned consistency = carl::satisfied_by(iter->first, mModel);
			if (consistency == 0) {
				splitUnequalConstraint(n);
				nr_splits++;
				if (nr_splits >= Settings::nr_neq_splits_at_once) break;
			} else if (consistency == 2) {
				// TODO: handle what happens if n contains variables not present in mModel
			}
		}
		return nr_splits > 0;
	}
} // namespace smtrat
