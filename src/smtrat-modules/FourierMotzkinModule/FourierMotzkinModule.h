/**
 * @file FourierMotzkinModule.h
 * @author valentin promies
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */

#pragma once

#include <smtrat-solver/Module.h>
#include "../NewFMPlexModule/NewFMPlexModule.h"
#include "Level.h"
#include "FourierMotzkinSettings.h"

namespace smtrat {
	template<typename Settings>
	class FourierMotzkinModule : public Module
	{
		private:
			// Members.
			std::vector<foumo::Level> m_history; 	/// stack representing the path to the current node
			std::size_t m_current_level; 			/// index of current level in history
			std::size_t m_max_level;				/// the maximum possible level (= number of eliminable variables)

			/// maps for converting tableau columns into variables and vice versa
			std::map<fmplex::ColumnIndex, carl::Variable> m_variable_order;
			std::map<carl::Variable, fmplex::ColumnIndex> m_variable_index;

			/// set of all variables ocurring in any of the received constraints
			carl::Variables m_variables;
			
			/// set of indices corresponding to strict inequalities in m_constraints
			std::unordered_set<std::size_t> m_strict_origins;

			/// sets of received formulas
			FormulasT m_constraints;
			FormulasT m_added_constraints; // REVIEW: is this necessary?
			std::set<std::size_t> m_disequalities; // TODO: indexing this way is inconvenient when removing constraints incrementally
			std::set<std::size_t> m_equalities;
			std::set<FormulaT> m_non_linear_constraints;

			Settings::gauss_type m_gauss;

			#ifdef SMTRAT_DEVOPTION_Statistics
			fmplex::FMPlexStatistics& m_statistics = fmplex::FMPlexStatistics::get_instance();
			#endif

			/**
			 * @brief stores the index of the most recently added constraint in m_disequalities or m_equalities,
			 * 			depending on the relation of that constraint.
			 * 
			 * @param r the relation of the most recently added constraint.
			 */
			void add_relation(carl::Relation r);

			/**
			 * @brief Constructs an unsatisfiable core (a.k.a. infeasible subset) from the given set of indices
			 * 
			 * @param reason A set of indices corresponding to an infeasible subset of m_constraints
			 */
			void build_unsat_core(const std::set<std::size_t>& reason);

			/**
			 * @brief stores the given level at the index of m_history
			 */
			void set_level(std::size_t index, const foumo::Level& level);

			/**
			 * @brief Constructs the root level of the FMPlex search tree.
			 * Depending on the Settings, applies Gaussian elimination to the equalities.
			 * Reserves enough space in m_history and constructs its first element, containing only inequalities.
			 * 
			 * @return a Conflict, if inconsistency can be easily determined after Gauss elimination, and nullopt otherwise.
			 */
			std::optional<foumo::Conflict> construct_root_level();

			/**
			 * @brief Checks whether the current model is consistent with the received not-equal constraints.
			 * Depending on the settings, if the model is not consistent, then splitting lemmas are passed to the SAT solver.
			 * 
			 * @return true if they are consistent
			 * @return false if not
			 */
			bool handle_neqs();

			/**
			 * 
			*/
			Rational find_suitable_delta(std::map<std::size_t, fmplex::DeltaRational> working_model) const;

			/**
			 * @brief Tries to construct a model from m_history if it contains a trivially satisfiable Level.
			 * 
			 * @return true if the model is consistent with the not-equal constraints
			 * @return false otherwise.
			 */
			bool try_construct_model();

		public:
			using SettingsType = Settings;

			FourierMotzkinModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = NULL);

			~FourierMotzkinModule();
			
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
