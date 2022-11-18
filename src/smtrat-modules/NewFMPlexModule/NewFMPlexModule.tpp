/**
 * @file NewFMPlex.cpp
 * @author valentin promies
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */
#pragma once

#include "NewFMPlexModule.h"
#include <eigen3/Eigen/Sparse>

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
		// todo: check for non-linear?
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
	void NewFMPlexModule<Settings>::init()
	{}
	
	template<class Settings>
	bool NewFMPlexModule<Settings>::addCore( ModuleInput::const_iterator _subformula ) {
		// todo: check for non-linear?
		switch (_subformula->formula().type()){
		case carl::FormulaType::TRUE:
			return true;
		case carl::FormulaType::FALSE: {
			FormulaSetT inf_subset;
			inf_subset.insert(_subformula->formula());
			mInfeasibleSubsets.push_back(inf_subset);
			return false;
		}
		case carl::FormulaType::CONSTRAINT: {
			// todo: other eq/neq handling NOTE: this works only for GAUSSIAN_TABLEAU and SPLITTING_LEMMAS
			m_constraints.push_back(_subformula->formula());
			// todo: check for trivial sat/unsat
			if constexpr (Settings::incremental) {
				m_added_constraints.push_back(_subformula->formula());
				// todo: watch out for incrementality
				// todo: need to apply Gauss to incrementally added ineq's
			}
			carl::Relation r = _subformula->formula().constraint().relation();
			if ((r == carl::Relation::LESS) || (r == carl::Relation::GREATER)) {
				m_strict_origins.insert(m_constraints.size()-1);
			} else if (r == carl::Relation::NEQ) m_neqs.push_back(_subformula->formula());
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
		for (const auto& v : m_elimination_variables) {
			mModel.emplace(v,0);
		}
		std::map<std::size_t, Rational> working_model;
		if (m_current_level > 0) {
			// use i-1, beginning with current_level - 1 as the current level should not contain any variables
			for (std::size_t i = m_current_level; i > 0; i--) {
				Rational v = m_history[i-1].find_variable_assignment(working_model);
				std::size_t elim_variable_index = m_history[i-1].eliminated_column_index();
				working_model.emplace(elim_variable_index, v);
				mModel.emplace(m_variable_order.at(elim_variable_index), v);
			}
		}
		// NOTE: NEQ handling can be done before EQ handling thanks to Gaussing
		if constexpr (Settings::eq_handling == EQHandling::GAUSSIAN_TABLEAU) {
			if (!m_gauss_order.empty()) {
				for (std::size_t i = m_gauss_order.size() - 1; i >= 0; i--) {
					auto [row, col] = m_gauss_order[i];
					std::vector<std::size_t> cols = m_initial_tableau.non_zero_variable_columns(row);
					for (const std::size_t j : cols) {
						if (!((j == col) || (working_model.count(j) == 1))) {
							working_model.emplace(j,0);
							mModel.emplace(m_variable_order[j],0);
						}
					}
					Rational v = m_initial_tableau.bound_value(row, col, working_model); // TODO: handle unassigned variables NOTE: take NEQs into account?
					working_model.emplace(col,v);
					mModel.emplace(m_variable_order.at(col), v);
				}
			}
		} else {
			// todo: not yet implemented
			assert(false);
		}

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
	Answer NewFMPlexModule<Settings>::checkCore() {
		// Incrementality
		if constexpr (Settings::incremental) {
			// todo: (low priority)
		} else {
			auto conflict = construct_root_level();
			if (conflict) {
				build_unsat_core(conflict->involved_rows);
				return Answer::UNSAT;
			}
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
					if (!try_construct_model()) return Answer::UNKNOWN;
				} // todo: else?
				return Answer::SAT;
			}

			m_history[m_current_level].choose_elimination_column();
			// TODO: retrieve eliminated vars from tableaus?

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
			if (m_history.size() <= m_current_level + 1) m_history.push_back(m_history[m_current_level].next_child());
			else m_history[m_current_level + 1] = m_history[m_current_level].next_child(); // REVIEW: construct inplace with reference parameters?
			m_current_level++;
		}
		assert(false); // unreachable
		return Answer::UNKNOWN;
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
			m_initial_tableau.apply_gaussian_elimination();
			for (std::size_t i = 0; i < m_initial_tableau.nr_of_rows(); i++) {
				auto [conflicting, _strict] = m_initial_tableau.is_row_conflict(i);
				if (conflicting) {
					return fmplex::Conflict{0, m_initial_tableau.origins(i).first};
				}
			}
			fmplex::FMPlexTableau root_tableau = m_initial_tableau.restrict_to_inequalities(); // TODO: only do this if there are eqs/neqs
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

	using SparseMatrix = Eigen::SparseMatrix<Rational, Eigen::ColMajor>;
	using Vector = Eigen::SparseVector<Rational>;

	/*template<class Settings>
	void NewFMPlexModule<Settings>::gaussian_elimination() { // REVIEW: make non-member?
		std::vector<Eigen::Triplet<Rational>> matrix_entries;
		std::vector<Eigen::Triplet<Rational>> vector_entries;
                    
		for (std::size_t row = 0; row < constraints.size(); row++) {
			const FormulaT& c = m_equalities[row];
			Poly p = c.constraint().lhs();
			for (const auto& term : p) {
				if (term.is_constant()) {
					vector_entries.emplace_back(term.coeff());
				} else {
					matrix_entries.emplace_back(row, m_variable_index.at(term.single_variable), term.coeff());
				}
			}
		}

		// TODO: inputs/outputs?
		// convert equalities to sparse matrix

		// use eigen to solve
		// how can we read off the origins?
		// somewhere else: use the result to transform neqs and ineqs
	}*/

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
} // namespace smtrat
