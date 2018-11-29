/**
 * @file MCBModule.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 *
 * Multiple-Choice Blasting
 * Detects arithmetic variabls that allow for a finite number of choices.
 * Blasts there choices to boolean variables.
 *
 * @version 2015-12-10
 * Created on 2015-12-10.
 */

#pragma once

#include "../PModule.h"
#include "MCBStatistics.h"
#include "MCBSettings.h"

namespace smtrat
{
	template<typename Settings>
	class MCBModule : public PModule
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			MCBStatistics mStatistics;
#endif
			using AVar = carl::Variable;
			using BVar = carl::Variable;
			
			std::map<AVar, std::map<Rational, std::pair<BVar,FormulaT>>> mChoices;
			std::set<AVar> mRemaining;
			mutable Model mAssignments;
			
		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			MCBModule(const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = nullptr);

			~MCBModule();

			/**
			 * Checks the received formula for consistency.
			 * @return SAT,	if the received formula is satisfiable;
			 *		 UNSAT,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
			Answer checkCore();
			void updateModel() const;
		private:
			void collectBounds(FormulaT::ConstraintBounds& cb, const FormulaT& formula, bool conjunction) const;
			void collectChoices(const FormulaT& formula);
			std::function<void(FormulaT)> collectChoicesFunction;
			FormulaT applyReplacements(const FormulaT& f);
	};
}
