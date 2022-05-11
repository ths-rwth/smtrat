/**
 * @file CSplitModule.cpp
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-11-01.
 */

#include "CSplitModule.h"

#include <carl/interval/set_theory.h>

namespace smtrat
{
	template<class Settings>
	CSplitModule<Settings>::CSplitModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager)
		: Module( _formula, _conditionals, _manager )
		, mPurifications()
		, mExpansions()
		, mLinearizations()
		, mVariableBounds()
		, mLRAModel()
		, mCheckedWithBackends(false)
	{}
	
	template<class Settings>
	bool CSplitModule<Settings>::addCore(ModuleInput::const_iterator _subformula)
	{
		addReceivedSubformulaToPassedFormula(_subformula);
		const FormulaT& formula{_subformula->formula()};
		if (formula.type() == carl::FormulaType::FALSE)
			mInfeasibleSubsets.push_back({formula});
		else if (formula.isBound())
		{
			/// Update the variable domain with the asserted bound
			mVariableBounds.addBound(formula, formula);
			const carl::Variable& variable{*formula.variables().begin()};
			auto expansionIter{mExpansions.firstFind(variable)};
			if (expansionIter == mExpansions.end())
				expansionIter = mExpansions.emplace(variable);
			expansionIter->mChangedBounds = true;
			if (mVariableBounds.isConflicting())
				mInfeasibleSubsets.emplace_back(mVariableBounds.getConflict());
		}
		else if (formula.type() == carl::FormulaType::CONSTRAINT)
		{
			/// Normalize the left hand side of the constraint and turn the relation accordingly
			const ConstraintT& constraint{formula.constraint()};
			const Poly normalization{constraint.lhs().normalize()};
			carl::Relation relation{constraint.relation()};
			if (carl::isNegative(constraint.lhs().lcoeff()))
				relation = carl::turn_around(relation);
			
			/// Purifiy and discretize the normalized left hand side to construct the linearization
			auto linearizationIter{mLinearizations.firstFind(normalization)};
			if (linearizationIter == mLinearizations.end())
			{
				Poly discretization;
				std::vector<Purification *> purifications;
				bool hasRealVariables{false};
				for (TermT term : normalization)
				{
					if (!term.isConstant())
					{
						size_t realVariables{0};
						for (const auto& exponent : term.monomial()->exponents())
							if (exponent.first.type() == carl::VariableType::VT_REAL)
								realVariables += exponent.second;
						if (realVariables)
						{
							term.coeff() /= carl::pow(Rational(Settings::discrDenom), realVariables);
							hasRealVariables = true;
						}
						
						if (!term.isLinear())
						{
							Purification& purification{mPurifications[term.monomial()]};
							purifications.emplace_back(&purification);
							term = term.coeff()*purification.mSubstitutions[0];
						}
						else if (realVariables)
						{
							const carl::Variable variable{term.getSingleVariable()};
							auto expansionIter{mExpansions.firstFind(variable)};
							if (expansionIter == mExpansions.end())
								expansionIter = mExpansions.emplace(variable);
							term = term.coeff()*expansionIter->mQuotients[0];
						}
					}
					discretization += term;
				}
				linearizationIter = mLinearizations.emplace(normalization, std::move(discretization.normalize()), std::move(purifications), hasRealVariables);
			}
			Linearization& linearization{*linearizationIter};
			propagateFormula(FormulaT(linearization.mLinearization, relation), true);
			if (linearization.mRelations.empty())
				for (Purification *purification : linearization.mPurifications)
					++purification->mUsage;
			linearization.mRelations.emplace(relation);
			
			/// Check if the asserted relation trivially conflicts with other asserted relations
			switch (relation)
			{
				case carl::Relation::EQ:
					if (linearization.mRelations.count(carl::Relation::NEQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::EQ),
							FormulaT(normalization, carl::Relation::NEQ)
						});
					if (linearization.mRelations.count(carl::Relation::LESS))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::EQ),
							FormulaT(normalization, carl::Relation::LESS)
						});
					if (linearization.mRelations.count(carl::Relation::GREATER))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::EQ),
							FormulaT(normalization, carl::Relation::GREATER)
						});
					break;
				case carl::Relation::NEQ:
					if (linearization.mRelations.count(carl::Relation::EQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::NEQ),
							FormulaT(normalization, carl::Relation::EQ)
						});
					break;
				case carl::Relation::LESS:
					if (linearization.mRelations.count(carl::Relation::EQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::LESS),
							FormulaT(normalization, carl::Relation::EQ)
						});
					if (linearization.mRelations.count(carl::Relation::GEQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::LESS),
							FormulaT(normalization, carl::Relation::GEQ)
						});
				case carl::Relation::LEQ:
					if (linearization.mRelations.count(carl::Relation::GREATER))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, relation),
							FormulaT(normalization, carl::Relation::GREATER)
						});
					break;
				case carl::Relation::GREATER:
					if (linearization.mRelations.count(carl::Relation::EQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::GREATER),
							FormulaT(normalization, carl::Relation::EQ)
						});
					if (linearization.mRelations.count(carl::Relation::LEQ))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, carl::Relation::GREATER),
							FormulaT(normalization, carl::Relation::LEQ)
						});
				case carl::Relation::GEQ:
					if (linearization.mRelations.count(carl::Relation::LESS))
						mInfeasibleSubsets.push_back({
							FormulaT(normalization, relation),
							FormulaT(normalization, carl::Relation::LESS)
						});
					break;
				default:
					assert(false);
			}
		}
		return mInfeasibleSubsets.empty();
	}
	
	template<class Settings>
	void CSplitModule<Settings>::removeCore(ModuleInput::const_iterator _subformula)
	{
		const FormulaT& formula{_subformula->formula()};	
		if (formula.isBound())
		{
			/// Update the variable domain with the removed bound
			mVariableBounds.removeBound(formula, formula);
			mExpansions.firstAt(*formula.variables().begin()).mChangedBounds = true;
		}
		else if (formula.type() == carl::FormulaType::CONSTRAINT)
		{
			/// Normalize the left hand side of the constraint and turn the relation accordingly
			const ConstraintT& constraint{formula.constraint()};
			const Poly normalization{constraint.lhs().normalize()};
			carl::Relation relation{constraint.relation()};
			if (carl::isNegative(constraint.lhs().lcoeff()))
				relation = carl::turn_around(relation);
			
			/// Retrieve the normalized constraint and mark the separator object as changed
			Linearization& linearization{mLinearizations.firstAt(normalization)};
			propagateFormula(FormulaT(linearization.mLinearization, relation), false);
			linearization.mRelations.erase(relation);
			if (linearization.mRelations.empty())
				for (Purification *purification : linearization.mPurifications)
					++purification->mUsage;
		}
	}
	
	template<class Settings>
	void CSplitModule<Settings>::updateModel() const
	{
		if(!mModelComputed)
		{
			clearModel();
			if (mCheckedWithBackends)
			{
				getBackendsModel();
				excludeNotReceivedVariablesFromModel();
			}
			else
			{
				for (const Expansion& expansion : mExpansions)
					if (receivedVariable(expansion.mRationalization))
					{
						Rational value{mLRAModel.at(expansion.mDiscretization).asRational()};
						if (expansion.mRationalization.type() == carl::VariableType::VT_REAL)
							value /= Settings::discrDenom;
						mModel.emplace(expansion.mRationalization, value);
					}
			}
			mModelComputed = true;
		}
	}
	
	template<class Settings>
	Answer CSplitModule<Settings>::checkCore()
	{
		/// Report unsatisfiability if the already found conflicts are still unresolved
		if (!mInfeasibleSubsets.empty())
			return Answer::UNSAT;
		
		/// Apply the method only if the asserted formula is not trivially undecidable
		if (rReceivedFormula().isConstraintConjunction())
		{
			mLRAModule.push();
			if (resetExpansions())
			{
				mCheckedWithBackends = false;
				for (size_t i = 1; i <= Settings::maxIter; ++i)
					if (mLRAModule.check(true) == Answer::SAT)
					{
						mLRAModel = mLRAModule.model();
						mLRAModule.pop();
						return Answer::SAT;
					}
					else
					{
						FormulaSetT conflict{mLRAModule.infeasibleSubsets()[0]};
						if (bloatDomains(conflict))
						{
							mLRAModule.pop();
							return analyzeConflict(conflict);
						}
					}
			}
			mLRAModule.pop();
		}
		
		/// Check the asserted formula with the backends
		mCheckedWithBackends = true;
		Answer answer{runBackends()};
		if (answer == Answer::UNSAT)
			getInfeasibleSubsets();
		
		return answer;
	}
	
	template<class Settings>
	bool CSplitModule<Settings>::resetExpansions()
	{
		/// Update the variable domains and watch out for discretization conflicts
		for (Expansion& expansion : mExpansions)
		{
			RationalInterval& maximalDomain{expansion.mMaximalDomain};
			if (expansion.mChangedBounds)
			{
				maximalDomain = mVariableBounds.getInterval(expansion.mRationalization);
				if (expansion.mRationalization.type() == carl::VariableType::VT_REAL)
					maximalDomain *= Rational(Settings::discrDenom);
				maximalDomain.integralPart_assign();
				if (expansion.mMaximalDomain.isUnbounded())
					expansion.mMaximalDomainSize = DomainSize::UNBOUNDED;
				else if (expansion.mMaximalDomain.diameter() > Settings::maxDomainSize)
					expansion.mMaximalDomainSize = DomainSize::LARGE;
				else
					expansion.mMaximalDomainSize = DomainSize::SMALL;
				expansion.mChangedBounds = false;
			}
			if (maximalDomain.isEmpty())
				return false;
			expansion.mActiveDomain = RationalInterval::emptyInterval();
			expansion.mPurifications.clear();
		}
		
		/// Activate all used purifications bottom-up
		for (auto purificationIter = mPurifications.begin(); purificationIter != mPurifications.end(); ++purificationIter)
		{
			Purification& purification{purificationIter->second};
			if (purification.mUsage)
			{
				carl::Monomial::Arg monomial{purificationIter->first};
				
				/// Find set of variables with maximal domain size
				carl::Variables maxVariables;
				DomainSize maxDomainSize{DomainSize::SMALL};
				for (const auto& exponent : monomial->exponents())
				{
					const carl::Variable& variable{exponent.first};
					auto expansionIter{mExpansions.firstFind(variable)};
					if (expansionIter == mExpansions.end())
						expansionIter = mExpansions.emplace(variable);
					Expansion& expansion{*expansionIter};
					
					if (maxDomainSize <= expansion.mMaximalDomainSize)
					{
						if (maxDomainSize < expansion.mMaximalDomainSize)
						{
							maxVariables.clear();
							maxDomainSize = expansion.mMaximalDomainSize;
						}
						maxVariables.emplace(variable);
					}
				}
				
				/// Find a locally optimal reduction for the monomial
				const auto isReducible = [&](const auto& purificationsEntry) {
					return purificationsEntry.second.mActive
						&& monomial->divisible(purificationsEntry.first)
						&& std::any_of(
							maxVariables.begin(),
							maxVariables.end(),
							[&](const carl::Variable& variable) {
								return purificationsEntry.first->has(variable);
							}
						);
				};
				auto reductionIter{std::find_if(std::make_reverse_iterator(purificationIter), mPurifications.rend(), isReducible)};
				
				/// Activate the sequence of reductions top-down
				carl::Monomial::Arg guidance;
				if (reductionIter == mPurifications.rend())
					monomial->divide(*maxVariables.begin(), guidance);
				else
					monomial->divide(reductionIter->first, guidance);
				auto hintIter{purificationIter};
				for (const auto& exponentPair : guidance->exponents())
				{
					const carl::Variable& variable{exponentPair.first};
					Expansion& expansion{mExpansions.firstAt(variable)};
					for (carl::exponent exponent = 1; exponent <= exponentPair.second; ++exponent)
					{
						hintIter->second.mActive = true;
						expansion.mPurifications.emplace_back(&hintIter->second);
						monomial->divide(variable, monomial);
						if (monomial->isAtMostLinear())
							hintIter->second.mReduction = mExpansions.firstAt(monomial->getSingleVariable()).mQuotients[0];
						else
						{
							auto temp{mPurifications.emplace_hint(hintIter, std::piecewise_construct, std::make_tuple(monomial), std::make_tuple())};
							hintIter->second.mReduction = temp->second.mSubstitutions[0];
							hintIter = temp;
						}
					}
				}
			}
			else
				purification.mActive = false;
		}
		
		/// Activate expansions that are used for case splits and deactivate them otherwise
		for (Expansion& expansion : mExpansions)
		{
			/// Calculate the center point where the initial domain is located
			expansion.mNucleus = 0;
			if (expansion.mMaximalDomain.lowerBoundType() != carl::BoundType::INFTY
				&& expansion.mNucleus < expansion.mMaximalDomain.lower())
				expansion.mNucleus = expansion.mMaximalDomain.lower();
			else if (expansion.mMaximalDomain.upperBoundType() != carl::BoundType::INFTY
				&& expansion.mNucleus > expansion.mMaximalDomain.upper())
				expansion.mNucleus = expansion.mMaximalDomain.upper();
			
			/// Calculate and activate the corresponding domain
			RationalInterval domain(0, 1);
			domain.mul_assign(carl::Interval<Rational>(Rational(Settings::initialRadius)));
			domain.add_assign(carl::Interval<Rational>(expansion.mNucleus));
			domain = carl::set_intersection(domain, expansion.mMaximalDomain);
			changeActiveDomain(expansion, std::move(domain));
		}
		
		return true;
	}
	
	template<class Settings>
	bool CSplitModule<Settings>::bloatDomains(const FormulaSetT& LRAConflict)
	{
		/// Data structure for potential bloating candidates
		struct Candidate
		{
			Expansion& mExpansion;
			const Rational mDirection;
			const Rational mRadius;
			
			Candidate(Expansion& expansion, Rational&& direction, Rational&& radius)
				: mExpansion(expansion)
				, mDirection(std::move(direction))
				, mRadius(std::move(radius))
			{}
			
			bool operator<(const Candidate& rhs) const
			{
				if (carl::isOne(mDirection*rhs.mDirection))
					return mRadius < rhs.mRadius;
				else if (carl::isOne(mDirection))
					return mRadius < Rational(Settings::thresholdRadius);
				else
					return rhs.mRadius >= Rational(Settings::thresholdRadius);
			}
		};
		std::set<Candidate> candidates;
		
		/// Scan the infeasible subset of the LRA solver for potential candidates
		for (const FormulaT& formula : LRAConflict)
			if (formula.isBound())
			{
				const ConstraintT& constraint{formula.constraint()};
				const carl::Variable variable{constraint.variables().as_vector().front()};
				auto expansionIter{mExpansions.secondFind(variable)};
				if (expansionIter != mExpansions.end())
				{
					Expansion& expansion{*expansionIter};
					Rational direction;
					if (carl::is_lower_bound(constraint)
						&& (expansion.mMaximalDomain.lowerBoundType() == carl::BoundType::INFTY
							|| expansion.mMaximalDomain.lower() < expansion.mActiveDomain.lower()))
						direction = -1;
					else if (carl::is_upper_bound(constraint)
						&& (expansion.mMaximalDomain.upperBoundType() == carl::BoundType::INFTY
							|| expansion.mMaximalDomain.upper() > expansion.mActiveDomain.upper()))
						direction  = 1;
					if (!carl::isZero(direction))
					{
						Rational radius{(direction*(expansion.mActiveDomain-expansion.mNucleus)).upper()};
						if (radius <= Settings::maximalRadius)
						{
							candidates.emplace(expansion, std::move(direction), std::move(radius));
							if (candidates.size() > Settings::maxBloatedDomains)
								candidates.erase(std::prev(candidates.end()));
						}
					}
				}
			}
		
		/// Change the active domain of the candidates with highest priority
		for (const Candidate& candidate : candidates)
		{
			RationalInterval domain;
			if (candidate.mRadius <= Settings::thresholdRadius)
				domain = RationalInterval(0, 1);
			else if (candidate.mExpansion.mPurifications.empty())
				domain = RationalInterval(0, carl::BoundType::WEAK, 0, carl::BoundType::INFTY);
			else
				domain = RationalInterval(0, candidate.mRadius);
			domain.mul_assign(carl::Interval<Rational>(candidate.mDirection));
			domain.add_assign(candidate.mExpansion.mActiveDomain);
			domain = carl::set_intersection(domain, candidate.mExpansion.mMaximalDomain);
			changeActiveDomain(candidate.mExpansion, std::move(domain));
		}
		
		/// Report if any variable domain was bloated
		return candidates.empty();
	}
	
	template<class Settings>
	Answer CSplitModule<Settings>::analyzeConflict(const FormulaSetT& LRAConflict)
	{
		FormulaSetT infeasibleSubset;
		for (const FormulaT& formula : LRAConflict)
		{
			if (formula.isBound())
			{
				auto expansionIter{mExpansions.secondFind(*formula.variables().begin())};
				if (expansionIter != mExpansions.end())
				{
					const Expansion& expansion{*expansionIter};
					if (expansion.mRationalization.type() == carl::VariableType::VT_REAL
						|| expansion.mMaximalDomain != expansion.mActiveDomain)
						return Answer::UNKNOWN;
					else
					{
						FormulaSetT boundOrigins{mVariableBounds.getOriginSetOfBounds(expansion.mRationalization)};
						infeasibleSubset.insert(boundOrigins.begin(), boundOrigins.end());
					}
				}
			}
			else if (formula.type() == carl::FormulaType::CONSTRAINT)
			{
				const ConstraintT& constraint{formula.constraint()};
				auto linearizationIter{mLinearizations.secondFind(constraint.lhs().normalize())};
				if (linearizationIter != mLinearizations.end())
				{
					const Linearization& linearization{*linearizationIter};
					if (linearization.mHasRealVariables)
						return Answer::UNKNOWN;
					else
					{
						carl::Relation relation{constraint.relation()};
						if (carl::isNegative(constraint.lhs().lcoeff()))
							relation = carl::turn_around(relation);
						infeasibleSubset.emplace(linearization.mNormalization, relation);
					}
				}
			}
		}
		mInfeasibleSubsets.emplace_back(std::move(infeasibleSubset));
		return Answer::UNSAT;
	}
	
	template<class Settings>
	void CSplitModule<Settings>::changeActiveDomain(Expansion& expansion, RationalInterval&& domain)
	{
		RationalInterval activeDomain{std::move(expansion.mActiveDomain)};
		expansion.mActiveDomain = domain;
		
		/// Update the variable bounds
		if (!activeDomain.isEmpty())
		{
			if (activeDomain.lowerBoundType() != carl::BoundType::INFTY
				&& (domain.lowerBoundType() == carl::BoundType::INFTY
					|| domain.lower() != activeDomain.lower()
					|| domain.isEmpty()))
				propagateFormula(FormulaT(expansion.mQuotients[0]-Poly(activeDomain.lower()), carl::Relation::GEQ), false);
			if (activeDomain.upperBoundType() != carl::BoundType::INFTY
				&& (domain.upperBoundType() == carl::BoundType::INFTY
					|| domain.upper() != activeDomain.upper()
					|| domain.isEmpty()))
				propagateFormula(FormulaT(expansion.mQuotients[0]-Poly(activeDomain.upper()), carl::Relation::LEQ), false);
		}
		if (!domain.isEmpty())
		{
			if (domain.lowerBoundType() != carl::BoundType::INFTY
				&& (activeDomain.lowerBoundType() == carl::BoundType::INFTY
					|| activeDomain.lower() != domain.lower()
					|| activeDomain.isEmpty()))
				propagateFormula(FormulaT(expansion.mQuotients[0]-Poly(domain.lower()), carl::Relation::GEQ), true);
			if (domain.upperBoundType() != carl::BoundType::INFTY
				&& (activeDomain.upperBoundType() == carl::BoundType::INFTY
					|| activeDomain.upper() != domain.upper()
					|| activeDomain.isEmpty()))
				propagateFormula(FormulaT(expansion.mQuotients[0]-Poly(domain.upper()), carl::Relation::LEQ), true);
		}
		
		/// Check if the digits of the expansion need to be encoded
		if (expansion.mPurifications.empty())
		{
			activeDomain = RationalInterval::emptyInterval();
			domain = RationalInterval::emptyInterval();
		}
		
		/// Update the case splits of the corresponding digits
		for (size_t i = 0; activeDomain != domain; ++i)
		{
			if (domain.diameter() <= Settings::maxDomainSize)
			{
				/// Update the currently active linear encoding
				Rational lower{activeDomain.isEmpty() ? domain.lower() : activeDomain.lower()};
				Rational upper{activeDomain.isEmpty() ? domain.lower() : activeDomain.upper()+1};
				for (const Purification *purification : expansion.mPurifications)
				{
					for (Rational alpha = domain.lower(); alpha < lower; ++alpha)
						propagateFormula(
							FormulaT(
								carl::FormulaType::IMPLIES,
								FormulaT(Poly(expansion.mQuotients[i])-Poly(alpha), carl::Relation::EQ),
								FormulaT(Poly(purification->mSubstitutions[i])-Poly(alpha)*Poly(purification->mReduction), carl::Relation::EQ)
							),
							true
						);
					for (Rational alpha = upper; alpha <= domain.upper(); ++alpha)
						propagateFormula(
							FormulaT(
								carl::FormulaType::IMPLIES,
								FormulaT(Poly(expansion.mQuotients[i])-Poly(alpha), carl::Relation::EQ),
								FormulaT(Poly(purification->mSubstitutions[i])-Poly(alpha)*Poly(purification->mReduction), carl::Relation::EQ)
							),
							true
						);
				}
			}
			else if (activeDomain.diameter() <= Settings::maxDomainSize)
			{
				/// Switch from the linear to a logarithmic encoding
				if (expansion.mQuotients.size() <= i+1)
				{
					expansion.mQuotients.emplace_back(carl::freshIntegerVariable());
					expansion.mRemainders.emplace_back(carl::freshIntegerVariable());
				}
				for (Purification *purification : expansion.mPurifications)
				{
					if (purification->mSubstitutions.size() <= i+1)
						purification->mSubstitutions.emplace_back(carl::freshIntegerVariable());
					for (Rational alpha = activeDomain.lower(); alpha <= activeDomain.upper(); ++alpha)
						propagateFormula(
							FormulaT(
								carl::FormulaType::IMPLIES,
								FormulaT(Poly(expansion.mQuotients[i])-Poly(alpha), carl::Relation::EQ),
								FormulaT(Poly(purification->mSubstitutions[i])-Poly(alpha)*Poly(purification->mReduction), carl::Relation::EQ)
							),
							false
						);
					for (Rational alpha = 0; alpha < Settings::expansionBase; ++alpha)
						propagateFormula(
							FormulaT(
								carl::FormulaType::IMPLIES,
								FormulaT(Poly(expansion.mRemainders[i])-Poly(alpha), carl::Relation::EQ),
								FormulaT(Poly(purification->mSubstitutions[i])-Poly(Settings::expansionBase)*Poly(purification->mSubstitutions[i+1])-Poly(alpha)*Poly(purification->mReduction), carl::Relation::EQ)
							),
							true
						);
				}
				propagateFormula(FormulaT(Poly(expansion.mQuotients[i])-Poly(Settings::expansionBase)*Poly(expansion.mQuotients[i+1])-Poly(expansion.mRemainders[i]), carl::Relation::EQ), true);
				propagateFormula(FormulaT(Poly(expansion.mRemainders[i]), carl::Relation::GEQ), true);
				propagateFormula(FormulaT(Poly(expansion.mRemainders[i])-Poly(Settings::expansionBase-1), carl::Relation::LEQ), true);
			}
			
			/// Calculate the domain of the next digit
			if (!activeDomain.isEmpty()) {
				if (activeDomain.diameter() <= Settings::maxDomainSize)
					activeDomain = RationalInterval::emptyInterval();
				else
					activeDomain = carl::floor(activeDomain/Rational(Settings::expansionBase));
			}
			if (!domain.isEmpty()) {
				if (domain.diameter() <= Settings::maxDomainSize)
					domain = RationalInterval::emptyInterval();
				else
					domain = carl::floor(domain/Rational(Settings::expansionBase));
			}
			
			/// Update the variable bounds of the next digit
			if (!activeDomain.isEmpty())
			{
				if (domain.isEmpty() || domain.lower() != activeDomain.lower())
					propagateFormula(FormulaT(expansion.mQuotients[i+1]-Poly(activeDomain.lower()), carl::Relation::GEQ), false);
				if (domain.isEmpty() || domain.upper() != activeDomain.upper())
					propagateFormula(FormulaT(expansion.mQuotients[i+1]-Poly(activeDomain.upper()), carl::Relation::LEQ), false);
			}
			if (!domain.isEmpty())
			{
				if (activeDomain.isEmpty() || activeDomain.lower() != domain.lower())
					propagateFormula(FormulaT(expansion.mQuotients[i+1]-Poly(domain.lower()), carl::Relation::GEQ), true);
				if (activeDomain.isEmpty() || activeDomain.upper() != domain.upper())
					propagateFormula(FormulaT(expansion.mQuotients[i+1]-Poly(domain.upper()), carl::Relation::LEQ), true);
			}
		}
	}
	
	template<class Settings>
	inline void CSplitModule<Settings>::propagateFormula(const FormulaT& formula, bool assert)
	{
		if (assert)
			mLRAModule.add(formula);
		else
			mLRAModule.remove(std::find(mLRAModule.formulaBegin(), mLRAModule.formulaEnd(), formula));
	}
}

#include "Instantiation.h"
