/**
 * 
 * Supports optimization.
 * 
 * @file PBPPModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-11-23
 * Created on 2016-11-23.
 */

#pragma once

#include <carl-arith/numbers/PrimeFactory.h>
#include <boost/math/common_factor.hpp>

#include "Encoders/CardinalityEncoder.h"
#include "Encoders/LongFormulaEncoder.h"
#include "Encoders/MixedSignEncoder.h"
#include "Encoders/RNSEncoder.h"
#include "Encoders/ShortFormulaEncoder.h"
#include "Encoders/ExactlyOneCommanderEncoder.h"
#include "Encoders/TotalizerEncoder.h"

#include <smtrat-solver/Module.h>

#include "PBPPSettings.h"
#include "PBPPStatistics.h"
#include "Encoders/PseudoBoolNormalizer.h"


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

			// the actual encodings by constraint. Does not contain any coupling. These are just substitutions.
			std::map<ConstraintT, FormulaT> boolEncodings;
			std::map<ConstraintT, FormulaT> liaConstraintFormula;

			std::map<ConstraintT, Rational> conversionSizeByConstraint;
			std::map<ConstraintT, PseudoBoolEncoder*> encoderByConstraint;
			std::map<ConstraintT, FormulaT> formulaByConstraint;

			RNSEncoder mRNSEncoder;
			ShortFormulaEncoder mShortFormulaEncoder;
			LongFormulaEncoder mLongFormulaEncoder;
			CardinalityEncoder mCardinalityEncoder;
			MixedSignEncoder mMixedSignEncoder;
			ExactlyOneCommanderEncoder mExactlyOneCommanderEncoder;
			TotalizerEncoder mTotalizerEncoder;

			PseudoBoolNormalizer mNormalizer;

			std::vector<PseudoBoolEncoder*> mEncoders;

		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			PBPPModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

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
			FormulaT convertSmallFormula(const ConstraintT& formula);
			FormulaT convertBigFormula(const ConstraintT& formula);

			FormulaT forwardAsArithmetic(const ConstraintT& formula, const std::set<carl::Variable>& boolVariables);

			FormulaT generateVarChain(const std::set<carl::Variable>& vars, carl::FormulaType type);
			FormulaT interconnectVariables(const std::set<carl::Variable>& variables);

			bool encodeAsBooleanFormula(const ConstraintT& constraint);
			bool isTrivial(const ConstraintT& constraint);

			void extractConstraints(const FormulaT& formula);

			void addConstraints(const FormulaT& formula);

			FormulaT restoreFormula(const FormulaT& formula);


	};
}
