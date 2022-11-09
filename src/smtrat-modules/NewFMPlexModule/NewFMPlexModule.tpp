/**
 * @file NewFMPlex.cpp
 * @author valentin promies
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */

#include "NewFMPlexModule.h"

namespace smtrat
{
	template<class Settings>
	NewFMPlexModule<Settings>::NewFMPlexModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
	{}
	
	template<class Settings>
	NewFMPlexModule<Settings>::~NewFMPlexModule()
	{}
	
	template<class Settings>
	bool NewFMPlexModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// gather information on variables
		constraint.gather_variables(m_variables);
		// TODO check for trivially false
		return true;
	}
	
	template<class Settings>
	void NewFMPlexModule<Settings>::init()
	{}
	
	template<class Settings>
	bool NewFMPlexModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		// TODO: check for trivial sat/unsat, add to initial tableau
		m_constraints.push_back(_subformula->formula()); // TODO check for duplicates?
		if constexpr (Settings::incremental) {
			m_added_constraints.push_back(_subformula->formula());
		}
		// TODO: watch out for incrementality
		return true;
	}
	
	template<class Settings>
	void NewFMPlexModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		auto it = m_constraints.find(_subformula->formula());
		if (it != m_constraints.end()) {
			m_constraints.erase(it);
		}
		// TODO: Incrementality
	}
	
	template<class Settings>
	void NewFMPlexModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			for (const auto& v : m_elimination_variables) {
				mModel.emplace(v,0);
			}
			for (std::size_t i = m_current_level; i >= 0; i--) {
				mModel.emplace(m_variable_order[i], m_history[i].find_variable_assignment(mModel));
			}
		}
	}
	
	template<class Settings>
	Answer NewFMPlexModule<Settings>::checkCore()
	{

		// Incrementality
		if constexpr (Settings::incremental) {
			// TODO (low priority)
		} else {
			construct_root_level();
		}

		// Main loop
		while(true) {
			auto conflict = m_history[m_current_level].earliest_conflict();
			if (conflict) {
				if (conflict->first == 0){ // global conflict => return unsat
					build_unsat_core(conflict->second);
					return Answer::UNSAT;
				}
				// local conflict => maybe backtrack
				if constexpr (Settings::use_backtracking) {
					// TODO: when storing the union of local conflicts, we need to handle the case that
					// a conflict is found which lets us backtrack higher, we might be able to discard
					// some of the previously found conflicts. => store info in each level?
					backtrack(conflict->first, conflict->second);
				}
			} else if (m_current_level == m_max_level) { // no conflict at max. level => SAT
			// TODO: also include the case that all variabes are already eliminated at a lower level
				construct_model();
				return Answer::SAT;
			}

			// move back to the most recent level with unchecked eliminators
			// checked_all_eliminators is also true if there are no variables left to eliminate
			while(m_history[m_current_level].checked_all_eliminators()) {
				// If all eliminators of the root level are checked, return UNSAT
				if (m_current_level == 0) {
					// TODO: UNSAT core
					return Answer::UNSAT;
				}
				m_current_level--;
			}
			
			if (!m_history[m_current_level].variable_chosen()) {
				choose_variable(m_history[m_current_level]);
			}
			m_history[m_current_level + 1] = m_history[m_current_level].next_child();
			m_current_level++;
		}
		assert(false); // unreachable
		return Answer::UNKNOWN;
	}

	template<class Settings>
	void NewFMPlexModule<Settings>::construct_root_level() {
		// TODO : check for redundancies -> in tableau?
		m_history.reserve(m_constraints.size());
		m_history[0] = Level(m_constraints); // construct root level
		if constexpr (Settings::eq_handling == EQ_Handling::GAUSSIAN) {
			gaussian_elimination();
		}
		m_current_level = 0;
		m_elimination_variables(m_variables);
	}

	template<class Settings>
	void NewFMPlexModule<Settings>::gaussian_elimination() {
		// TODO: inputs/outpus?
	}

}
