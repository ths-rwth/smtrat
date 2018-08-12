/**
 * @file PBPPModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-11-23
 * Created on 2016-11-23.
 */

#pragma once

#include <carl/numbers/PrimeFactory.h>
#include <boost/math/common_factor.hpp>

#include "CardinalityEncoder.h"
#include "LongFormulaEncoder.h"
#include "MixedSignEncoder.h"
#include "../../solver/Module.h"
#include "PBPPStatistics.h"
#include "PBPPSettings.h"
#include "RNSEncoder.h"
#include "ShortFormulaEncoder.h"


namespace smtrat
{
	template<typename Settings>
		class PBPPModule : public Module
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			PBPPStatistics mStatistics;
#endif
			// Members.
			std::map<carl::Variable, carl::Variable> mVariablesCache; // int, bool
			std::vector<carl::Variable> mCheckedVars;
			std::vector<carl::Variable> mConnectedVars;

    		std::vector<ConstraintT> liaConstraints;
			std::vector<ConstraintT> boolConstraints;
			std::vector<ConstraintT> mConstraints;

			std::map<ConstraintT, Rational> conversionSizeByConstraint;
			std::map<ConstraintT, PseudoBoolEncoder*> encoderByConstraint;
			std::map<ConstraintT, FormulaT> formulaByConstraint;

			RNSEncoder mRNSEncoder;
			ShortFormulaEncoder mShortFormulaEncoder;
			LongFormulaEncoder mLongFormulaEncoder;
			CardinalityEncoder mCardinalityEncoder;
			MixedSignEncoder mMixedSignEncoder;

			std::vector<PseudoBoolEncoder*> encoders = { &mCardinalityEncoder };

		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			PBPPModule(const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = nullptr);

			~PBPPModule();

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

		private:
			bool isAllCoefficientsEqual(const ConstraintT& constraint);
			FormulaT convertPbConstraintToConstraintFormula(const FormulaT& formula);
			FormulaT convertSmallFormula(const ConstraintT& formula);
			FormulaT convertBigFormula(const ConstraintT& formula);

			FormulaT forwardAsArithmetic(const ConstraintT& formula);

			FormulaT checkFormulaType(const FormulaT& formula);
			FormulaT checkFormulaTypeWithRNS(const FormulaT& formula);
			FormulaT checkFormulaTypeWithCardConstr(const FormulaT& formula);
			FormulaT checkFormulaTypeWithMixedConstr(const FormulaT& formula);
			FormulaT checkFormulaTypeBasic(const FormulaT& formula);

			FormulaT checkFormulaAndApplyTransformations(const FormulaT& subformula);
			FormulaT generateVarChain(const std::set<carl::Variable>& vars, carl::FormulaType type);
			FormulaT createAuxiliaryConstraint(const std::vector<carl::Variable>& variables);
			FormulaT interconnectVariables(const std::set<carl::Variable>& variables);

			FormulaT encodeCardinalityConstraint(const ConstraintT& formula);
			FormulaT encodeMixedConstraints(const ConstraintT& formula);
			FormulaT encodeConstraintOrForwardAsArithmetic(const ConstraintT& constraint, PseudoBoolEncoder& encoder);

			bool encodeAsBooleanFormula(const ConstraintT& constraint);
			bool isTrivial(const ConstraintT& constraint);

	};
}
