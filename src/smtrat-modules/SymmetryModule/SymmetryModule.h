/**
 * @file SymmetryModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-03-12
 * Created on 2018-03-12.
 */

#pragma once

#include <smtrat-solver/PModule.h>
#include "SymmetryStatistics.h"
#include "SymmetrySettings.h"

namespace smtrat
{
	template<typename Settings>
	class SymmetryModule : public PModule
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			SymmetryStatistics mStatistics;
#endif
		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			SymmetryModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

			~SymmetryModule();
			
			// Main interfaces.
			/**
			 * Checks the received formula for consistency.
			 * @return True,	if the received formula is satisfiable;
			 *		 False,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
			Answer checkCore();
	};
}
