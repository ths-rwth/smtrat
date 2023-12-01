/**
 * @file QuantifierCoveringModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2023-04-17
 * Created on 2023-04-17.
 */

#pragma once

#include <carl-arith/ran/Conversion.h>
#include <carl-formula/formula/functions/Substitution.h>
#include <smtrat-common/types.h>
#include <smtrat-coveringng/Algorithm.h>
#include "smtrat-coveringng/VariableOrdering.h"
#include <smtrat-modules/QuantifierCoveringModule/QuantifierCoveringSettings.h>
#include <smtrat-solver/Module.h>
#include "smtrat-coveringng/FormulaEvaluation.h"
#include "smtrat-coveringng/FormulaEvaluationComplexity.h"
#include "smtrat-coveringng/types.h"
#include <algorithm>
#include <carl-formula/formula/FormulaContent.h>
#include <queue>


namespace smtrat
{
	template<typename Settings>
	class QuantifierCoveringModule : public Module
	{
		private:
			covering_ng::VariableQuantification mVariableQuantification;
			
		public:
			using SettingsType = Settings;

			QuantifierCoveringModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

			~QuantifierCoveringModule();

			bool informCore( const FormulaT& _constraint );

			void init();

			bool addCore( ModuleInput::const_iterator _subformula );

			void removeCore( ModuleInput::const_iterator _subformula );

			void updateModel() const;

			Answer checkCore();
	};
}
