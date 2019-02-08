/**
 * @file GBPPModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-03-09
 * Created on 2018-03-09.
 */

#pragma once

#include <smtrat-solver/PModule.h>
#include "GBPPStatistics.h"
#include "GBPPSettings.h"

namespace smtrat
{
	template<typename Settings>
	class GBPPModule : public PModule
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			GBPPStatistics mStatistics;
#endif
			FormulaSetT mEqualities;
			std::size_t mEqualityComplexity = 0;
			FormulaSetT mRest;
			typename Settings::Groebner mBasis;
			
			auto gpoly(const Poly& p) const {
				return typename Settings::PolynomialWithReasons(p);
			}
			
		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			GBPPModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

			~GBPPModule();

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

		private:
			FormulaT simplifyInequality(const FormulaT& formula) const;
			std::function<FormulaT(const FormulaT&)> simplifyInequalityFunction;
	};
}
