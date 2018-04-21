/**
 * @file CSplitModule.cpp
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-11-01.
 */

#include "CSplitModule.h"

namespace smtrat
{
	template<class Settings>
	CSplitModule<Settings>::CSplitModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager)
		: Module( _formula, _conditionals, _manager )
		, mCheckedWithBackends(false)
		, mExpansions()
		, mExpansionsSource(mExpansions.template get<0>())
		, mExpansionsTarget(mExpansions.template get<1>())
		, mLinearizations()
		, mLinearizationsSource(mLinearizations.template get<0>())
		, mLinearizationsTarget(mLinearizations.template get<1>())
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	bool CSplitModule<Settings>::addCore(ModuleInput::const_iterator _subformula)
	{
		addReceivedSubformulaToPassedFormula(_subformula);
		const FormulaT& formula{_subformula->formula()};
		if (formula.getType() == carl::FormulaType::FALSE)
			mInfeasibleSubsets.push_back({formula});
		else if (formula.getType() == carl::FormulaType::CONSTRAINT)
		{
			const ConstraintT& constraint{formula.constraint()};
			
			if (constraint.isBound())
			{
				mVariableBounds.addBound(constraint, formula);
				const carl::Variable& variable{*constraint.variables().begin()};
				auto expansionIter{mExpansionsSource.find(variable)};
				if (expansionIter == mExpansionsSource.end())
					expansionIter = mExpansionsSource.emplace(variable).first;
				expansionIter->mChangedBounds = true;
				if (mVariableBounds.isConflicting())
					mInfeasibleSubsets.emplace_back(mVariableBounds.getConflict());
			}
			else
			{/*
				/// Normalize the left hand side of the constraint and turn the relation accordingly
				const Poly normalization{constraint.lhs().normalize()};
				carl::Relation relation{constraint.relation()};
				if (carl::isNegative(constraint.lhs().lcoeff()))
					relation = carl::turnAroundRelation(relation);
				
				auto linearizationIter{mLinearizations.firstFind(normalization)};
				if (linearizationIter == mLinearizations.end())
				{
					Poly discretization;
					std::vector<Purification *> purifications;
					bool hasRealVariables{false};
					for (const TermT& term : normalization)
					{
						const carl::Monomial::Arg& monomial{term.monomial()};
						if (monomial)
						{
							Rational coefficient{term.coeff()};
							size_t realVariables{0};
							for (const auto& exponent : monomial->exponents())
								if (exponent.first.type() == carl::VariableType::VT_REAL)
									realVariables += exponent.second;
							if (realVariables)
							{
								coefficient *= carl::pow(Rational(1, Settings::discrDenom), realVariables);
								hasRealVariables = true;
							}
							
							carl::Variable substitution;
							if (!monomial->isLinear())
							{
								Purification& purification{mPurifications[monomial]};
								purifications.emplace_back(&purification);
								substitution = purification.mSubstitutions[0];
							}
							else if (realVariables)
								substitution = mExpansions.firstFind(monomial->getSingleVariable())->first.second;
							else
								substitution = monomial->getSingleVariable();
							
							discretization += coefficient*substitution;
						}
						else
							discretization += term;
					}
					linearizationIter = mLinearizations.emplace(normalization, discretization, std::move(purifications), std::move(hasRealVariables));
				}
				Linearization& linearization{linearizationIter->second};
				linearization.mRelations.emplace(relation);
				mChangedLinearizations.emplace(&linearization);
				
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
				}*/
			}
		}
		return mInfeasibleSubsets.empty();
	}
	
	template<class Settings>
	void CSplitModule<Settings>::removeCore(ModuleInput::const_iterator _subformula)
	{/*
		const FormulaT& formula{_subformula->formula()};
		if (formula.getType() == carl::FormulaType::CONSTRAINT)
		{
			const ConstraintT& constraint{formula.constraint()};
			
			if (constraint.isBound())
			{
				mVariableBounds.removeBound(constraint, formula);
				mExpansions.firstFind(*constraint.variables().begin())->second.mChangedBounds = true;
			}
			else
			{
				/// Normalize the left hand side of the constraint and turn the relation accordingly
				const Poly normalization{constraint.lhs().normalize()};
				carl::Relation relation{constraint.relation()};
				if (carl::isNegative(constraint.lhs().lcoeff()))
					relation = carl::turnAroundRelation(relation);
				
				/// Retrieve the normalized constraint and mark the separator object as changed
				Linearization& linearization{mLinearizations.at(normalization)};
				linearization.mRelations.erase(relation);
				mChangedLinearizations.insert(&linearization);
			}
		}*/
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
				const Model& LRAModel{mLRAModule.model()};
				for (const Expansion& expansion : mExpansions)
					if (receivedVariable(expansion.mSource))
					{
						Rational value{LRAModel.at(expansion.mTarget).asRational()};
						if (expansion.mSource.type() == carl::VariableType::VT_REAL)
							value /= Settings::discrDenom;
						mModel.emplace(expansion.mSource, value);
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
		
		if (rReceivedFormula().isConstraintConjunction() && resetExpansions())
		{
			mCheckedWithBackends = false;
			for (size_t i = 1; i <= Settings::maxIter; ++i)
				if (mLRAModule.check(true) == Answer::SAT)
					return Answer::SAT;
				else
				{
					FormulaSetT conflict{mLRAModule.infeasibleSubsets()[0]};
					if (bloatDomains(conflict))
						return analyzeConflict(conflict);
				}
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
	{/*
		// Update bounds and check for discretization conflict
		for (auto& expansionsEntry : mExpansions)
		{
			Expansion& expansion{expansionsEntry.second};
			RationalInterval& maximalDomain{expansion.mMaximalDomain};
			if (expansion.mBoundsChanged)
			{
				const carl::Variable& variable{expansionsEntry.first};
				maximalDomain = mVariableBounds.getInterval(variable);
				if (variable.type() == carl::VariableType::VT_REAL)
					maximalDomain *= Rational(Settings::discrDenom);
				maximalDomain.integralPart_assign();
				expansion.mBoundsChanged = false;
			}
			if (maximalDomain.isEmpty())
				return false;
			expansion.mPurifications.clear();
		}
		
		mLRAModule.pop();
		for (Linearization *linearizationPtr : mChangedLinearizations)
		{
			Linearization& linearization{*linearizationPtr};
			
			boost::optional<carl::Relation> relation; 
			if (!linearization.mRelations.empty())
			{
				if (!linearization.mActiveRelation)
					for (Purification *purification : linearization.mPurifications)
						++purification->mUsage;				
				if (linearization.mRelations.count(carl::Relation::EQ)
					|| (linearization.mRelations.count(carl::Relation::LEQ)
						&& linearization.mRelations.count(carl::Relation::GEQ)))
					relation = carl::Relation::EQ;
				else if (linearization.mRelations.count(carl::Relation::LESS))
					relation = carl::Relation::LESS;
				else if (linearization.mRelations.count(carl::Relation::GREATER))
					relation = carl::Relation::GREATER;
				else
					relation = *linearization.mRelations.rbegin();
			}
			else if (linearization.mActiveRelation)
				for (Purification *purification : linearization.mPurifications)
					--purification->mUsage;
							
			if (linearization.mActiveRelation != relation)
			{
				if (linearization.mActiveRelation)
					propagateFormula(FormulaT(linearization.mLinearization, *linearization.mActiveRelation), false);
				linearization.mActiveRelation = relation;
				if (relation)
					propagateFormula(FormulaT(linearization.mLinearization, *relation), true);
			}
		}
		mChangedLinearizations.clear();
		mLRAModule.push();
		
		// Activate all asserted purifications bottom-up
		for (auto purificationIter = mPurifications.rbegin(); purificationIter != mPurifications.rend(); ++purificationIter)
		{
			Purification& purification{purificationIter->second};
			if (purification.mUsage)
			{
				carl::Monomial::Arg monomial{purificationIter->first};
				
				// Find set of variables with maximal domain
				enum DomainSize{SMALL = 0, LARGE = 1, UNBOUNDED = 2};
				carl::Variables maxVariables;
				DomainSize maxDomainSize{SMALL};
				for (const auto& exponent : monomial->exponents())
				{
					const carl::Variable& variable{exponent.first};
					const RationalInterval& maximalDomain{mExpansions[variable].mMaximalDomain};
					
					// Find size of the current variable domain
					DomainSize domainSize;
					if (maximalDomain.isUnbounded())
						domainSize = UNBOUNDED;
					else if (maximalDomain.diameter() > Settings::maxDomainSize)
						domainSize = LARGE;
					else
						domainSize = SMALL;
					
					// Update maximal domain
					if (maxDomainSize <= domainSize)
					{
						if (maxDomainSize < domainSize)
						{
							maxVariables.clear();
							maxDomainSize = domainSize;
						}
						maxVariables.emplace(variable);
					}
				}
				
				// Find locally optimal reduction for monomial
				const auto isReducible = [&](const auto& purificationsEntry) {
					return purificationsEntry.second.mUsage
						&& monomial->divisible(purificationsEntry.first)
						&& std::any_of(
							maxVariables.begin(),
							maxVariables.end(),
							[&](const carl::Variable& variable) {
								return purificationsEntry.first->has(variable);
							}
						);
				};
				auto reductionIter{std::find_if(purificationIter.base(), mPurifications.end(), isReducible)};
				
				// Construct sequence of purifications
				carl::Variable reduction;
				if (reductionIter == mPurifications.end())
				{
					const carl::Variable& maxVariable{*maxVariables.begin()};
					reduction = mExpansions.at(maxVariable).mQuotients[0];
					monomial = carl::createMonomial(maxVariable, 1);
				}
				else
				{
					reduction = reductionIter->second.mSubstitutions[0];
					monomial = reductionIter->first;
				}
				carl::Monomial::Arg guidance;
				purificationIter->first->divide(monomial, guidance);
				
				for (const auto& exponentPair : guidance->exponents())
				{
					const carl::Variable& variable{exponentPair.first};
					Expansion& expansion{mExpansions.at(variable)};
					for (carl::exponent exponent = 1; exponent <= exponentPair.second; ++exponent)
					{
						monomial = monomial*variable;
						Purification& purification{mPurifications[monomial]};
						purification.mReduction = reduction;
						reduction = purification.mSubstitutions[0];
						expansion.mPurifications.emplace(&purification);
					}
				}
			}
		}
		
		// Activate expansions that are used for case splits and deactivate them otherwise
		for (auto& expansionsEntry : mExpansions)
		{
			Expansion& expansion{expansionsEntry.second};
			
			// Calculate the nucleus where the initial domain is located
			expansion.mNucleus = ZERO_RATIONAL;
			if (expansion.mMaximalDomain.lowerBoundType() != carl::BoundType::INFTY
				&& expansion.mNucleus < expansion.mMaximalDomain.lower())
				expansion.mNucleus = expansion.mMaximalDomain.lower();
			else if (expansion.mMaximalDomain.upperBoundType() != carl::BoundType::INFTY
				&& expansion.mNucleus > expansion.mMaximalDomain.upper())
				expansion.mNucleus = expansion.mMaximalDomain.upper();
			
			// Calculate corresponding active domain
			RationalInterval domain(0, 1);
			domain.mul_assign(Rational(Settings::initialRadius));
			domain.add_assign(expansion.mNucleus);
			domain.intersect_assign(expansion.mMaximalDomain);
			expansion.mActiveDomain = RationalInterval::emptyInterval();
			changeActiveDomain(expansion, std::move(domain));
		}
		*/
		return true;
	}
	
	template<class Settings>
	bool CSplitModule<Settings>::bloatDomains(const FormulaSetT& LRAConflict)
	{
		// Data structure for potential bloating candidates
		struct Candidate
		{
			const Expansion& mExpansion;
			const Rational mDirection;
			const Rational mRadius;
			
			Candidate(const Expansion& expansion, Rational&& direction, Rational&& radius)
				: mExpansion(expansion)
				, mDirection(std::move(direction))
				, mRadius(std::move(radius))
			{}
			
			bool operator<(const Candidate& rhs) const
			{
				if (mDirection*rhs.mDirection == ONE_RATIONAL)
					return mRadius < rhs.mRadius;
				else if (mDirection == ONE_RATIONAL)
					return mRadius < Rational(Settings::thresholdRadius);
				else
					return rhs.mRadius >= Rational(Settings::thresholdRadius);
			}
		};
		std::set<Candidate> candidates;
		
		for (const FormulaT& formula : LRAConflict)
			if (formula.isBound())
			{
				const ConstraintT& constraint{formula.constraint()};
				const carl::Variable& variable{*constraint.variables().begin()};
				auto expansionIter{mExpansionsTarget.find(variable)};
				if (expansionIter != mExpansionsTarget.end())
				{
					const Expansion& expansion{*expansionIter};
					Rational direction;
					if (constraint.isLowerBound()
						&& (expansion.mMaximalDomain.lowerBoundType() == carl::BoundType::INFTY
							|| expansion.mMaximalDomain.lower() < expansion.mActiveDomain.lower()))
						direction = MINUS_ONE_RATIONAL;
					else if (constraint.isUpperBound()
						&& (expansion.mMaximalDomain.upperBoundType() == carl::BoundType::INFTY
							|| expansion.mMaximalDomain.upper() > expansion.mActiveDomain.upper()))
						direction  = ONE_RATIONAL;
					if (direction != ZERO_RATIONAL)
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
		
		for (const Candidate& candidate : candidates)
		{
			RationalInterval domain;
			if (candidate.mRadius <= Settings::thresholdRadius)
				domain = RationalInterval(0, Settings::radiusIncrement);
			else if (candidate.mExpansion.mPurifications.empty())
				domain = RationalInterval(0, carl::BoundType::WEAK, 0, carl::BoundType::INFTY);
			else
				domain = RationalInterval(0, candidate.mRadius);
			domain.mul_assign(candidate.mDirection);
			domain.add_assign(candidate.mExpansion.mActiveDomain);
			domain.intersect_assign(candidate.mExpansion.mMaximalDomain);
			changeActiveDomain(candidate.mExpansion, std::move(domain));
		}
		
		return candidates.empty();
	}
	
	template<class Settings>
	Answer CSplitModule<Settings>::analyzeConflict(const FormulaSetT& LRAConflict)
	{
		FormulaSetT infeasibleSubset;
		for (const FormulaT& formula : LRAConflict)
			if (formula.getType() == carl::FormulaType::CONSTRAINT)
			{
				const ConstraintT& constraint{formula.constraint()};
				if (formula.isBound())
				{
					const carl::Variable& variable{*constraint.variables().begin()};
					auto expansionIter{mExpansionsTarget.find(variable)};
					if (expansionIter != mExpansionsTarget.end())
					{
						const Expansion& expansion{*expansionIter};
						if (expansion.mSource.type() == carl::VariableType::VT_REAL
							|| expansion.mMaximalDomain != expansion.mActiveDomain)
							return Answer::UNKNOWN;
						else
						{
							FormulaSetT boundOrigins{mVariableBounds.getOriginSetOfBounds(variable)};
							infeasibleSubset.insert(boundOrigins.begin(), boundOrigins.end());
						}
					}
				}
				else
				{
					const Poly& polynomial{constraint.lhs().normalize()};
					auto linearizationIter{mLinearizationsTarget.find(polynomial)};
					if (linearizationIter != mLinearizationsTarget.end())
					{
						const Linearization& linearization{*linearizationIter};
						if (linearization.mHasRealVariables)
							return Answer::UNKNOWN;
						else
							infeasibleSubset.emplace(linearization.mSource, *linearization.mActiveRelation);
					}
				}
			}
		mInfeasibleSubsets.emplace_back(std::move(infeasibleSubset));
		return Answer::UNSAT;
	}
	
	template<class Settings>
	void CSplitModule<Settings>::changeActiveDomain(const Expansion& expansion, RationalInterval&& domain)
	{
		// Update variable bounds
		if (!expansion.mActiveDomain.isEmpty())
		{
			if (expansion.mActiveDomain.lowerBoundType() != carl::BoundType::INFTY
				&& (domain.lowerBoundType() == carl::BoundType::INFTY
					|| domain.lower() != expansion.mActiveDomain.lower()
					|| domain.isEmpty()))
				propagateFormula(FormulaT(expansion.mQuotients[0]-Poly(expansion.mActiveDomain.lower()), carl::Relation::GEQ), false);
			if (expansion.mActiveDomain.upperBoundType() != carl::BoundType::INFTY
				&& (domain.upperBoundType() == carl::BoundType::INFTY
					|| domain.upper() != expansion.mActiveDomain.upper()
					|| domain.isEmpty()))
				propagateFormula(FormulaT(expansion.mQuotients[0]-Poly(expansion.mActiveDomain.upper()), carl::Relation::LEQ), false);
		}
		if (!domain.isEmpty())
		{
			if (domain.lowerBoundType() != carl::BoundType::INFTY
				&& (expansion.mActiveDomain.lowerBoundType() == carl::BoundType::INFTY
					|| expansion.mActiveDomain.lower() != domain.lower()
					|| expansion.mActiveDomain.isEmpty()))
				propagateFormula(FormulaT(expansion.mQuotients[0]-Poly(domain.lower()), carl::Relation::GEQ), true);
			if (domain.upperBoundType() != carl::BoundType::INFTY
				&& (expansion.mActiveDomain.upperBoundType() == carl::BoundType::INFTY
					|| expansion.mActiveDomain.upper() != domain.upper()
					|| expansion.mActiveDomain.isEmpty()))
				propagateFormula(FormulaT(expansion.mQuotients[0]-Poly(domain.upper()), carl::Relation::LEQ), true);
		}
		
		// Update case splits
		if (expansion.mPurifications.empty())
			expansion.mActiveDomain = std::move(domain);
		else
		{
			RationalInterval activeDomain{std::move(expansion.mActiveDomain)};
			expansion.mActiveDomain = domain;
			
			for (size_t i = 0; activeDomain != domain; ++i)
			{
				if (domain.diameter() <= Settings::maxDomainSize)
				{
					// Update existing linear encoding
					for (const Purification *purification : expansion.mPurifications)
					{
						for (Rational alpha = domain.lower(); alpha < activeDomain.lower(); ++alpha)
							propagateFormula(
								FormulaT(
									carl::FormulaType::IMPLIES,
									FormulaT(Poly(expansion.mQuotients[i])-Poly(alpha), carl::Relation::EQ),
									FormulaT(Poly(purification->mSubstitutions[i])-Poly(alpha)*Poly(purification->mReduction), carl::Relation::EQ)
								),
								true
							);
						for (Rational alpha = activeDomain.upper()+ONE_RATIONAL; alpha <= domain.upper(); ++alpha)
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
					// Switch from linear to logarithmic encoding
					if (expansion.mQuotients.size() <= i+1)
					{
						expansion.mQuotients.emplace_back(carl::freshIntegerVariable());
						expansion.mRemainders.emplace_back(carl::freshIntegerVariable());
					}
					for (Purification *purification : expansion.mPurifications)
					{
						while (purification->mSubstitutions.size() <= i+1)
							purification->mSubstitutions.emplace_back(carl::freshIntegerVariable());/////////////////////////////////////////////////////////////
						for (Rational alpha = activeDomain.lower(); alpha <= activeDomain.upper(); ++alpha)
							propagateFormula(
								FormulaT(
									carl::FormulaType::IMPLIES,
									FormulaT(Poly(expansion.mQuotients[i])-Poly(alpha), carl::Relation::EQ),
									FormulaT(Poly(purification->mSubstitutions[i])-Poly(alpha)*Poly(purification->mReduction), carl::Relation::EQ)
								),
								false
							);
						for (Rational alpha = ZERO_RATIONAL; alpha < Settings::expansionBase; ++alpha)
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
				
				// Calculate domain of next digit
				if (!activeDomain.isEmpty())
					if (activeDomain.diameter() <= Settings::maxDomainSize)
						activeDomain = RationalInterval::emptyInterval();
					else
						activeDomain = carl::floor(activeDomain/Rational(Settings::expansionBase));
				if (!domain.isEmpty())
					if (domain.diameter() <= Settings::maxDomainSize)
						domain = RationalInterval::emptyInterval();
					else
						domain = carl::floor(domain/Rational(Settings::expansionBase));
				
				// Update variable bounds of next digit
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
	}
	
	template<class Settings>
	inline void CSplitModule<Settings>::propagateFormula(const FormulaT& formula, bool assert)
	{
		if (assert)
			mLRAModule.add(formula);
		else
			mLRAModule.remove(find(mLRAModule.formulaBegin(), mLRAModule.formulaEnd(), formula));
	}
}

#include "Instantiation.h"
