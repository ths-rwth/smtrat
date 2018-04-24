/**
 * @file CSplitModule.h
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-11-01.
 */

#pragma once

#include <boost/optional.hpp>
#include "../../datastructures/VariableBounds.h"
#include "../../solver/Module.h"
#include "../../solver/Manager.h"
#include "../SATModule/SATModule.h"
#include "../LRAModule/LRAModule.h"
#include "Bimap.h"
#include "CSplitStatistics.h"
#include "CSplitSettings.h"

namespace smtrat
{
	template<typename Settings>
	class CSplitModule : public Module
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			CSplitStatistics mStatistics;
#endif
			/**
			 * Represents the substitution variables of a nonlinear monomial
			 * in a positional notation to the basis Settings::expansionBase.
			 */
			struct Purification
			{
				std::vector<carl::Variable> mSubstitutions;
				carl::Variable mReduction;
				size_t mUsage;
				bool mActive;
				
				Purification()
					: mSubstitutions()
					, mReduction(carl::Variable::NO_VARIABLE)
					, mUsage(0)
					, mActive(false)
				{
					mSubstitutions.emplace_back(carl::freshIntegerVariable());
				}
			};
			
			std::map<carl::Monomial::Arg, Purification> mPurifications;
			
			/// Subdivides the size of a variable domain into three classes:
			/// - SMALL, 	 if domain size <= Settings::maxDomainSize
			/// - LARGE, 	 if Settings::maxDomainSize < domain size < infinity
			/// - UNBOUNDED, if domain size = infinity
			enum DomainSize{SMALL = 0, LARGE = 1, UNBOUNDED = 2};
			
			/**
			 * Represents the quotients and remainders of a variable in
			 * a positional notation to the basis Settings::expansionBase.
			 */
			struct Expansion
			{
				const carl::Variable mSource, mTarget;
				Rational mNucleus;
				DomainSize mMaximalDomainSize;
				RationalInterval mMaximalDomain, mActiveDomain;
				std::vector<carl::Variable> mQuotients, mRemainders;
				std::vector<Purification *> mPurifications;
				bool mChangedBounds;
				
				Expansion(const carl::Variable& source)
					: mSource(source)
					, mTarget(source.type() == carl::VariableType::VT_INT ? source : carl::freshIntegerVariable())
					, mNucleus(ZERO_RATIONAL)
					, mMaximalDomainSize(DomainSize::UNBOUNDED)
					, mMaximalDomain(RationalInterval::unboundedInterval())
					, mActiveDomain(RationalInterval::emptyInterval())
					, mChangedBounds(false)
				{
					mQuotients.emplace_back(mTarget);
				}
			};
			
			Bimap<Expansion, const carl::Variable, &Expansion::mSource, const carl::Variable, &Expansion::mTarget> mExpansions;
			
			/**
			 * Represents the class of all original constraints with the same
			 * left hand side after a normalization. Here, the set of all received
			 * relations of constraints with the same left hand side is stored.
			 */
			struct Linearization
			{
				const Poly mSource, mTarget;
				const std::vector<Purification *> mPurifications;
				const bool mHasRealVariables;
				std::unordered_set<carl::Relation> mRelations;
				
				Linearization(const Poly& source, Poly&& target, std::vector<Purification *>&& purifications, bool hasRealVariables)
					: mSource(source)
					, mTarget(std::move(target))
					, mPurifications(std::move(purifications))
					, mHasRealVariables(std::move(hasRealVariables))
				{}
			};
			
			Bimap<Linearization, const Poly, &Linearization::mSource, const Poly, &Linearization::mTarget> mLinearizations;
			
			/// Helper class that extracts the variable domains
			vb::VariableBounds<FormulaT> mVariableBounds;
			/// Stores the last model for the linearization that was found by the LRA solver
			Model mLRAModel;
			/// Stores whether the last consistency check was done by the backends
			bool mCheckedWithBackends;
			
			/**
			 * Linear arithmetic module to call for the linearized formula.
			 */
			struct LAModule : public Manager
			{
				LAModule() : Manager()
				{
					setStrategy({
						addBackend<SATModule<SATSettings1>>({
							addBackend<LRAModule<LRASettings1>>()
						})
					});
				}
			};
			
			/// Handle to the linear arithmetic module
			LAModule mLRAModule;
			
		public:
			typedef Settings SettingsType;
			
			std::string moduleName() const
			{
				return SettingsType::moduleName;
			}
			
			CSplitModule(const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = nullptr);
			
			/**
			 * The module has to take the given sub-formula of the received formula into account.
			 * @param _subformula The sub-formula to take additionally into account.
			 * @return False, if it can be easily decided that this sub-formula causes a conflict with
			 *				  the already considered sub-formulas;
			 *		   True, otherwise.
			 */
			bool addCore( ModuleInput::const_iterator _subformula );
			
			/**
			 * Removes the subformula of the received formula at the given position to the considered ones of this module.
			 * Note that this includes every stored calculation which depended on this subformula, but should keep the other
			 * stored calculation, if possible, untouched.
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
			 *		   False,   if the received formula is not satisfiable;
			 *		   Unknown, otherwise.
			 */
			Answer checkCore();
		
		private:
			bool resetExpansions();
			bool bloatDomains(const FormulaSetT& LRAConflict);
			Answer analyzeConflict(const FormulaSetT& LRAConflict);
			void changeActiveDomain(Expansion& expansion, RationalInterval&& domain);
			inline void propagateFormula(const FormulaT& formula, bool assert);
	};
}
