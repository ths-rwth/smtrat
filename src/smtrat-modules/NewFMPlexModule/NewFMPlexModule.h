/**
 * @file NewFMPlexModule.h
 * @author valentin promies
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */

#pragma once

#include <smtrat-solver/Module.h>
#include "NewFMPlexSettings.h"
//#include "Tableau.h"
#include "Level.h"

namespace smtrat {
	template<typename Settings>
	class NewFMPlexModule : public Module
	{
		private:
			// Members.
			// stack representing the path to the current node
			std::vector<fmplex::Level> m_history;
			// map for converting between constraints and their tableau index
			std::map<FormulaT,std::size_t> m_constraint_index;
			// index of current level in history
			std::size_t m_current_level;

			std::size_t m_max_level;
			// variable ordering in the tableaus
			std::map<std::size_t, carl::Variable> m_variable_order;
			std::map<carl::Variable, std::size_t> m_variable_index;

			carl::Variables m_variables;
			// set of remaining variables to eliminate
			carl::Variables m_elimination_variables;

			std::unordered_set<std::size_t> m_strict_origins;
			// 
			FormulasT m_constraints;
			FormulasT m_added_constraints; // REVIEW: is this necessary?
			FormulasT m_neqs;
			FormulasT m_equalities;

			fmplex::FMPlexTableau m_initial_tableau;
			std::vector<std::pair<fmplex::RowIndex, fmplex::ColumnIndex>> m_gauss_order;
			// REVIEW: datastructure to keep track, which eliminated variable corresponds to which constraint

			void build_unsat_core(const std::set<std::size_t>& reason);
			void backtrack(const fmplex::Conflict& conflict);
			std::optional<fmplex::Conflict> construct_root_level();
			// void gaussian_elimination();
			bool handle_neqs();
			bool try_construct_model();

		public:
			using SettingsType = Settings;

			NewFMPlexModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = NULL);

			~NewFMPlexModule();
			
			// Main interfaces.
			/**
			 * Informs the module about the given constraint. It should be tried to inform this
			 * module about any constraint it could receive eventually before assertSubformula
			 * is called (preferably for the first time, but at least before adding a formula
			 * containing that constraint).
			 * @param _constraint The constraint to inform about.
			 * @return false, if it can be easily decided whether the given constraint is inconsistent;
			 *		  true, otherwise.
			 */
			bool informCore( const FormulaT& _constraint );

			/**
			 * Informs all backends about the so far encountered constraints, which have not yet been communicated.
			 * This method must not and will not be called more than once and only before the first runBackends call.
			 */
			void init();

			/**
			 * The module has to take the given sub-formula of the received formula into account.
			 *
			 * @param _subformula The sub-formula to take additionally into account.
			 * @return false, if it can be easily decided that this sub-formula causes a conflict with
			 *		  the already considered sub-formulas;
			 *		  true, otherwise.
			 */
			bool addCore( ModuleInput::const_iterator _subformula );

			/**
			 * Removes the subformula of the received formula at the given position to the considered ones of this module.
			 * Note that this includes every stored calculation which depended on this subformula, but should keep the other
			 * stored calculation, if possible, untouched.
			 *
			 * @param _subformula The position of the subformula to remove.
			 */
			void removeCore( ModuleInput::const_iterator _subformula );

			/**
			 * Updates the current assignment into the model.
			 * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
			 */
			void updateModel() const;

			/**
			 * Checks the received formula for consistency.
			 * @return True,	if the received formula is satisfiable;
			 *		 False,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
			Answer checkCore();
	};
} // namespace smtrat
