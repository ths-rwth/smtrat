/**
 * @file MaxSMTModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2019-01-25
 * Created on 2019-01-25.
 */

#pragma once

#include "../Module.h"
#include "MaxSMTStatistics.h"
#include "MaxSMTSettings.h"

#include <smtrat-modules/PBPPModule/PBPPModule.h>

namespace smtrat
{
	template<typename Settings>
	class MaxSMTModule : public Module
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			MaxSMTStatistics mStatistics;
#endif
			// Members.
			std::vector<FormulaT> softclauses;
			std::map<FormulaT, carl::Variable> blockingVars;
			std::map<FormulaT, ModuleInput::iterator> formulaPositionMap;

			typename Settings::Backend mBackend;
			
		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			MaxSMTModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

			~MaxSMTModule();
			
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

			std::vector<FormulaT> runFuMalik();
			std::vector<FormulaT> runOLL();
			std::vector<FormulaT> runMSU3();
			std::vector<FormulaT> runLinearSearch();
			bool isSoft(const FormulaT& formula);
			void addSoftFormula(const FormulaT& formula);
			std::vector<FormulaT> gatherSatisfiedSoftClauses();
			ModuleInput::iterator addToLocalBackend(const FormulaT& formula);

			FormulasT getUnsatCore();

	};
}
