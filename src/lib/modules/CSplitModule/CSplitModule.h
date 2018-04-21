/**
 * @file CSplitModule.h
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-11-01.
 */

#pragma once

#include <boost/multi_index_container.hpp>
#include <boost/multi_index/hashed_index.hpp>
#include <boost/multi_index/member.hpp>
#include <boost/optional.hpp>
#include "../../datastructures/VariableBounds.h"
#include "../../solver/Module.h"
#include "../../solver/Manager.h"
#include "CSplitStatistics.h"
#include "CSplitSettings.h"
#include "../SATModule/SATModule.h"
#include "../LRAModule/LRAModule.h"

namespace smtrat
{
	template<typename Settings>
	class CSplitModule : public Module
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			CSplitStatistics mStatistics;
#endif
			template<typename Key, typename Value>
			using MultiIndex = boost::multi_index_container<
				Value,
				boost::multi_index::indexed_by<
					boost::multi_index::hashed_unique<
						boost::multi_index::member<Value, const Key, &Value::mSource>,
						std::hash<Key>,
						std::equal_to<Key>
					>,
					boost::multi_index::hashed_unique<
						boost::multi_index::member<Value, const Key, &Value::mTarget>,
						std::hash<Key>,
						std::equal_to<Key>
					>
				>
			>;
			
			template<typename Key, typename Value>
			using SourceIndex = typename MultiIndex<Key, Value>::template nth_index<0>::type&;
			
			template<typename Key, typename Value>
			using TargetIndex = typename MultiIndex<Key, Value>::template nth_index<1>::type&;
			
			struct Purification
			{
				std::vector<carl::Variable> mSubstitutions;
				carl::Variable mReduction;
				size_t mUsage;
				
				Purification()
					: mReduction(carl::Variable::NO_VARIABLE)
					, mUsage(0)
				{
					mSubstitutions.emplace_back(carl::freshIntegerVariable());
				}
			};
			
			std::map<carl::Monomial::Arg, Purification> mPurifications;
			
			struct Expansion
			{
				const carl::Variable mSource, mTarget;
				mutable Rational mNucleus;
				mutable RationalInterval mMaximalDomain, mActiveDomain;
				mutable std::vector<carl::Variable> mQuotients, mRemainders;
				mutable std::unordered_set<Purification *> mPurifications;
				mutable bool mChangedBounds;
				
				Expansion(const carl::Variable& source)
					: mNucleus(ZERO_RATIONAL)
					, mSource(source)
					, mTarget(source.type() == carl::VariableType::VT_INT ? source : carl::freshIntegerVariable())
					, mMaximalDomain(RationalInterval::unboundedInterval())
					, mActiveDomain(RationalInterval::emptyInterval())
					, mChangedBounds(false)
				{
					mQuotients.emplace_back(mTarget);
				}
			};
			
			MultiIndex<carl::Variable, Expansion> mExpansions;
			const SourceIndex<carl::Variable, Expansion> mExpansionsSource;
			const TargetIndex<carl::Variable, Expansion> mExpansionsTarget;
			
			struct Linearization
			{
				const Poly mSource, mTarget;
				const std::vector<Purification *> mPurifications;
				const bool mHasRealVariables;
				mutable std::set<carl::Relation> mRelations;
				mutable boost::optional<carl::Relation> mActiveRelation;
				
				Linearization(const Poly& source, Poly&& target, std::vector<Purification *>&& purifications, bool hasRealVariables)
					: mSource(source)
					, mTarget(std::move(target))
					, mPurifications(std::move(purifications))
					, mHasRealVariables(std::move(hasRealVariables))
				{}
			};
			
			MultiIndex<Poly, Linearization> mLinearizations;
			const SourceIndex<Poly, Linearization> mLinearizationsSource;
			const TargetIndex<Poly, Linearization> mLinearizationsTarget;
			
			std::unordered_set<Linearization *> mChangedLinearizations;
			
			vb::VariableBounds<FormulaT> mVariableBounds;
			
			// Stores whether the last consistency check was done by the backends
			bool mCheckedWithBackends;
			
			/**
			 * Linear arithmetic module to call for the linearized formula
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
			void changeActiveDomain(const Expansion& expansion, RationalInterval&& domain);
			inline void propagateFormula(const FormulaT& formula, bool assert);
	};
}
