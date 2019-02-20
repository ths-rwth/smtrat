/**
 * @file LVEModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2019-02-20
 * Created on 2019-02-20.
 */

#pragma once

#include <smtrat-solver/PModule.h>
#include "LVESettings.h"
#include "LVEStatistics.h"

namespace smtrat
{
	template<typename Settings>
	class LVEModule : public PModule
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			LVEStatistics& mStatistics = statistics_get<LVEStatistics>("lve");
#endif
			Model mPPModel;
			
			void count_variables(std::map<carl::Variable, std::size_t>& count, const ConstraintT& c) const;
			std::map<carl::Variable, std::size_t> get_variable_counts() const;
			std::vector<carl::Variable> get_lone_variables() const;
		
			std::optional<FormulaT> eliminate_variable(carl::Variable v, const ConstraintT& c);

			FormulaT eliminate_from_separated_weak_inequality(carl::Variable v, const Poly& with, const Poly& without, carl::Relation rel);
			FormulaT eliminate_from_separated_disequality(carl::Variable v, const Poly& with, const Poly& without);
			FormulaT eliminate_from_separated_strict_inequality(carl::Variable v, const Poly& with, const Poly& without, carl::Relation rel);
			std::optional<FormulaT> eliminate_from_separated_factors(carl::Variable v, const Poly& with, const Poly& without, carl::Relation rel);
			std::optional<FormulaT> eliminate_from_factors(carl::Variable v, const ConstraintT& c);

			std::optional<FormulaT> eliminate_linear(carl::Variable v, const ConstraintT& c);
		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			LVEModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

			~LVEModule();
			
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
}
