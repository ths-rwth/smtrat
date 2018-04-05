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
        , mLRAModule()
        , mCheckedWithBackends(false)
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	bool CSplitModule<Settings>::addCore(ModuleInput::const_iterator _subformula)
	{
        const FormulaT& origin{_subformula->formula()};
        const ConstraintT& constraint{origin.constraint()};
        
        for (const auto& variable : constraint.variables())
        {
            carl::Variable& discretization{mDiscretizations[variable]};
            if (discretization == carl::Variable::NO_VARIABLE)
            {
                discretization = variable.type() == carl::VariableType::VT_INT ? variable : carl::freshIntegerVariable();
                mExpansions.emplace(piecewise_construct, forward_as_tuple(discretization), forward_as_tuple(discretization, variable));
            }
        }
        
        if (constraint.isBound())
            mVariableBounds.addBound(constraint, origin);
        else
        {
            auto linearizationIter{mLinearizations.find(origin)};
            if (linearizationIter == mLinearizations.end())
            {
                const Poly& origPoly{constraint.lhs()};
                
                // Discretize real valued variables
                map<carl::Variable, TermT> discretizations;
                for (const auto& variable : origPoly.gatherVariables())
                    if (variable.type() == carl::VariableType::VT_REAL)
                    {
                        discretizations.emplace(
                            piecewise_construct,
                            forward_as_tuple(variable),
                            forward_as_tuple(Rational{1, Settings::discrDenom}, mDiscretizations.at(variable), 1)
                        );
                    }
                Poly discrPoly{origPoly.substitute(discretizations)};
                
                // Purify discretized polynomial
                Poly purePoly;
                vector<Purification *> purifications;
                for (auto term : discrPoly)
                    if (term.isLinear())
                        purePoly += Poly(move(term));
                    else
                    {
                        carl::Monomial::Arg monomial{term.monomial()};
                        auto iter{mPurifications.find(monomial)};
                        if (iter == mPurifications.end())
                            iter = mPurifications.emplace(monomial, carl::freshIntegerVariable()).first;
                        purePoly += term.coeff()*iter->second.mSubstitutions[0];
                        purifications.push_back(&iter->second);
                    }
                linearizationIter = mLinearizations.emplace(
                    piecewise_construct,
                    forward_as_tuple(origin),
                    forward_as_tuple(FormulaT(move(purePoly), constraint.relation()), move(purifications))
                ).first;
            }
            Linearization& linearization{linearizationIter->second};
            if (linearization.mUsage == 0)
            {
                propagateFormula(linearization.mLinearization, true);
                for (Purification *purification : linearization.mPurifications)
                    ++purification->mUsage;
            }
            ++linearization.mUsage;
        }
        addSubformulaToPassedFormula(origin, origin);
        
        if (mVariableBounds.isConflicting())
        {
            mInfeasibleSubsets.clear();
            mInfeasibleSubsets.push_back(mVariableBounds.getConflict());
            return false;
        }
        else
            return true;
	}
	
	template<class Settings>
	void CSplitModule<Settings>::removeCore(ModuleInput::const_iterator _subformula)
	{
        const FormulaT& origin{_subformula->formula()};
        const ConstraintT& constraint{origin.constraint()};
        
        if (constraint.isBound())
            mVariableBounds.removeBound(constraint, origin);
        else
        {
            Linearization& linearization{mLinearizations.at(origin)};
            --linearization.mUsage;
            if (linearization.mUsage == 0)
            {
                propagateFormula(linearization.mLinearization, false);
                for (Purification *purification : linearization.mPurifications)
                    --purification->mUsage;
            }
        }
	}
	
	template<class Settings>
	void CSplitModule<Settings>::updateModel() const
	{
        mModel.clear();
		if(solverState() == Answer::SAT)
		{
            if (mCheckedWithBackends)
                getBackendsModel();
            else
            {
                for (const auto& assignment : mLastModel)
                {
                    const auto expansionIter{mExpansions.find(assignment.first.asVariable())};
                    if (expansionIter != mExpansions.end())
                    {
                        const Expansion& expansion{expansionIter->second};
                        if (expansion.mDiscretization == expansion.mRationalization)
                            mModel.insert(assignment);
                        else
                            mModel.emplace(expansion.mRationalization, assignment.second.asRational()/Settings::discrDenom);
                    }
                }
                excludeNotReceivedVariablesFromModel();
            }
		}
	}
	
	template<class Settings>
	Answer CSplitModule<Settings>::checkCore()
	{
        //cout << "CHECKCORE CALLED" << endl;
        static size_t runs = 0;
        Answer answer = Answer::UNKNOWN;
        mCheckedWithBackends = false;
        mLRAModule.push();
        
        if (resetExpansions())
        {/*
            cout << "-------------- THE BOUNDS (INITIAL) ---------------------" << endl;
                        for (auto& expansion : mExpansions)
                        {
                            cout << "VAR: " << expansion.first << "   MAX: " << expansion.second.mMaximalDomain << "   ACTIVE: " << expansion.second.mActiveDomain << endl;
                        }*/
            for (size_t i = 1; i <= Settings::maxIter; ++i)
            {
                //cout << "CALLING LRA SOLVER" << endl;
                if (mLRAModule.check(true) == Answer::SAT)
                {
                    //cout << "ANSWERED SAT" << endl << endl;
                    mLastModel = mLRAModule.model();
                    answer = Answer::SAT;
                    break;
                }
                else
                {
                    // Analyze infeasible subset
                    FormulaSetT conflict{mLRAModule.infeasibleSubsets()[0]};
                    if (bloatDomains(conflict) == 0)
                    {
                        answer = analyzeConflict(conflict);
                        break;
                    }
/*
                        cout << "-------------- THE BOUNDS (AFTER CHANGE) ---------------------" << endl;
                        for (auto& expansion : mExpansions)
                        {
                            cout << "VAR: " << expansion.first << "   MAX: " << expansion.second.mMaximalDomain << "   ACTIVE: " << expansion.second.mActiveDomain << endl;
                        }
                        static size_t runs = 0;
                        cout << "RUNS: " << ++runs << endl << endl;*/
                }
            }
        }
        mLRAModule.pop();
        if (answer == Answer::UNKNOWN)
        {
            answer = runBackends();
            mCheckedWithBackends = true;
            if (answer == Answer::UNSAT)
                getInfeasibleSubsets();
        }
        return answer;
	}
    
    template<class Settings>
    bool CSplitModule<Settings>::resetExpansions()
    {
        for (auto& expansionPair : mExpansions)
        {
            expansionPair.second.mPurifications.clear();
            expansionPair.second.mActiveDomain = RationalInterval::emptyInterval();
        }
        
        // Update maximal bounds
        for (const auto& bound : mVariableBounds.getEvalIntervalMap())
        {
            carl::Variable variable{bound.first};
            RationalInterval maximalDomain{bound.second};
            if (variable.type() == carl::VariableType::VT_REAL)
            {
                variable = mDiscretizations.at(variable);
                maximalDomain *= Rational(Settings::discrDenom);
            }
            maximalDomain = maximalDomain.integralPart();
            if (maximalDomain.isEmpty())
                return false;
            else
                mExpansions.at(variable).mMaximalDomain = move(maximalDomain);
        }
        
        // Activate all asserted purifications bottom-up
        for (auto backwardIter = mPurifications.rbegin(); backwardIter != mPurifications.rend(); ++backwardIter)
        {
            Purification& purification{backwardIter->second};
            if (purification.mUsage > 0)
            {
                carl::Monomial::Arg monomial{backwardIter->first};
                // Find set of variables with maximal domain
                enum DomainSize{SMALL = 0, LARGE = 1, UNBOUNDED = 2};
                carl::Variables maxVariables;
                DomainSize maxDomainSize{SMALL};
                for (const auto& exponent : monomial->exponents())
                {
                    const carl::Variable& variable{exponent.first};
                    DomainSize domainSize;
                    
                    // Find size of the current variable domain
                    const RationalInterval& maximalDomain{mExpansions.at(variable).mMaximalDomain};
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
                        maxVariables.insert(variable);
                    }
                }
                // Find locally optimal reduction for monomial
                auto forwardIter{backwardIter.base()};
                function<bool()> isReducible = [&] () bool {
                        if (forwardIter->second.mUsage > 0
                            && monomial->divisible(forwardIter->first))
                            for (const auto& variable : maxVariables)
                                if (forwardIter->first->has(variable))
                                    return true;
                        return false;
                    };
                while (forwardIter != mPurifications.end() && !isReducible())
                    ++forwardIter;
                // Construct sequence of purifications
                if (forwardIter == mPurifications.end())
                {
                    const carl::Variable& variable{*maxVariables.begin()};
                    forwardIter = mPurifications.emplace(carl::createMonomial(variable, 1), variable).first;
                }
                monomial->divide(forwardIter->first, monomial);
                for (const auto& exponentPair : monomial->exponents())
                {
                    const carl::Variable& variable{exponentPair.first};
                    Expansion& expansion{mExpansions.at(variable)};
                    for (carl::exponent exponent = 1; exponent <= exponentPair.second; ++exponent)
                    {
                        carl::Monomial::Arg nextMonomial{forwardIter->first*variable};
                        auto nextIter = mPurifications.find(nextMonomial);
                        if (nextIter == mPurifications.end())
                            nextIter = mPurifications.emplace(nextMonomial, carl::freshIntegerVariable()).first;
                        nextIter->second.mReduction = &forwardIter->second;
                        nextIter->second.mExpansion = &expansion;
                        forwardIter = nextIter;
                        /*if (expansion.mActive)
                        {
                            RationalInterval activeDomain{expansion.mActiveDomain};
                            for (size_t i = 0; !activeDomain.isEmpty(); ++i)
                                if (activeDomain.diameter() <= Settings::maxDomainSize)
                                {
                                    propagateLinearCaseSplits(forwardIter->second, activeDomain, i, true);
                                    activeDomain = RationalInterval::emptyInterval();
                                }
                                else
                                {
                                    propagateLogarithmicCaseSplits(forwardIter->second, i, true);
                                    activeDomain = carl::floor(activeDomain/Rational(Settings::expansionBase));
                                }
                        }*/
                        expansion.mPurifications.insert(&forwardIter->second);
                    }
                }
            }
        }
        
        // Activate expansions that are used for case splits and deactivate them otherwise
        for (auto& bound : mExpansions)
        {
            Expansion& expansion{bound.second};
            
            // Calculate the nucleus where the initial domain is located
            /*auto modelIter{mLastModel.find(bound.first)};
            if (modelIter != mLastModel.end())
                expansion.mNucleus = modelIter->second.asRational();
            else
                expansion.mNucleus = ZERO_RATIONAL;*/
            
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
            changeActiveDomain(expansion, domain);
        }
        
        mLastModel.clear();
        
        return true;
    }
    
    template<class Settings>
    size_t CSplitModule<Settings>::bloatDomains(const FormulaSetT& conflict)
    {
        // Data structure for potential bloating candidates
        struct Candidate
        {
            Expansion *mExpansion; //////////////////////// REFERENCE!!!!
            Rational mDirection;
            Rational mRadius;
            
            Candidate(Expansion* expansion, Rational direction)
                : mExpansion(expansion)
                , mDirection(direction)
                , mRadius((mDirection*(mExpansion->mActiveDomain-mExpansion->mNucleus)).upper())
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
        
        vector<Candidate> candidates;
        for (const FormulaT& formula : conflict)
            if (formula.isBound())
            {
                const ConstraintT& constraint{formula.constraint()};
                const carl::Variable& variable{*constraint.variables().begin()};
                auto expansionIter{mExpansions.find(variable)};
                if (expansionIter != mExpansions.end())
                {
                    Expansion& expansion{expansionIter->second};
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
                        Candidate candidate(&expansion, direction);
                        if (candidate.mRadius <= Settings::maximalRadius)
                            candidates.push_back(candidate);
                    }
                }
            }
        size_t bloatedDomains{min(candidates.size(), Settings::maxBloatedDomains)};
        std::partial_sort(candidates.begin(), candidates.begin()+bloatedDomains, candidates.end());
        for (size_t i = 0; i < bloatedDomains; ++i)
        {
            Candidate& candidate{candidates[i]};
            Expansion& expansion{*candidate.mExpansion};
            RationalInterval domain;
            if (candidate.mRadius <= Settings::thresholdRadius)
                domain = RationalInterval(0, Settings::radiusIncrement);
            else if (expansion.mPurifications.empty())
                domain = RationalInterval(0, carl::BoundType::WEAK, 0, carl::BoundType::INFTY);
            else
                domain = RationalInterval(0, candidate.mRadius);
            domain.mul_assign(candidate.mDirection);
            domain.add_assign(expansion.mActiveDomain);
            domain.intersect_assign(expansion.mMaximalDomain);
            //cout << "CHANGING FROM " << expansion.mActiveDomain << " TO " << domain << endl;
            changeActiveDomain(expansion, domain);
        }
        return bloatedDomains;
    }
    
    template<class Settings>
    Answer CSplitModule<Settings>::analyzeConflict(const FormulaSetT& conflict)
    {
        FormulaSetT infeasibleSubset;
        for (const auto& transformation : mLinearizations)
        {
            const FormulaT& origin{transformation.first};
            const Linearization& linearization{transformation.second};
            if (linearization.mUsage > 0)
                if (origin.constraint().hasRealValuedVariable())
                    return Answer::UNKNOWN;
                else if (conflict.count(linearization.mLinearization) > 0)
                    infeasibleSubset.emplace_hint(infeasibleSubset.cend(), origin);
        }
        for (const FormulaT& formula : conflict)
            if (formula.isBound())
            {
                const ConstraintT& constraint{formula.constraint()};
                carl::Variable variable{*constraint.variables().begin()};
                auto expansionIter{mExpansions.find(variable)};
                if (expansionIter != mExpansions.end())
                {
                    const Expansion& expansion{expansionIter->second};
                    if (expansion.mMaximalDomain != expansion.mActiveDomain
                        || expansion.mDiscretization != expansion.mRationalization)
                        return Answer::UNKNOWN;
                    else
                    {
                        FormulaSetT boundOrigins{mVariableBounds.getOriginSetOfBounds(variable)};
                        infeasibleSubset.insert(boundOrigins.begin(), boundOrigins.end());
                    }
                }
            }
        mInfeasibleSubsets.clear();
        mInfeasibleSubsets.push_back(infeasibleSubset);
        return Answer::UNSAT;
    }
    
    template<class Settings>
    void CSplitModule<Settings>::changeActiveDomain(Expansion& expansion, RationalInterval domain)
    {
        RationalInterval activeDomain{move(expansion.mActiveDomain)};
        expansion.mActiveDomain = domain;
        
        // Update variable bounds
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
        
        // Check if digits need to be encoded
        if (expansion.mPurifications.empty())
        {
            activeDomain = RationalInterval::emptyInterval();
            domain = RationalInterval::emptyInterval();
        }
        
        // Update case splits
        for (size_t i = 0; activeDomain != domain; ++i)
        {
            if (activeDomain.diameter() <= Settings::maxDomainSize)
                if (domain.diameter() <= Settings::maxDomainSize)
                {
                    // Update existing linear encoding
                    RationalInterval intervalA, intervalB;
                    bool assertA{true}, assertB{false};
                    if (!domain.isEmpty())
                        assertB = domain.difference(activeDomain, intervalA, intervalB);
                    if (!assertB && !activeDomain.isEmpty())
                        assertA = !activeDomain.difference(domain, intervalB, intervalA);
                    intervalA.integralPart_assign();
                    intervalB.integralPart_assign();
                    for (Purification *purification : expansion.mPurifications)
                    {
                        propagateLinearCaseSplits(*purification, intervalA, i, assertA);
                        propagateLinearCaseSplits(*purification, intervalB, i, assertB);
                    }
                }
                else
                {
                    // Switch from linear to logarithmic encoding
                    if (expansion.mQuotients.size() <= i+1)
                    {
                        expansion.mQuotients.push_back(carl::freshIntegerVariable());
                        expansion.mRemainders.push_back(carl::freshIntegerVariable());
                    }
                    for (Purification *purification : expansion.mPurifications)
                    {
                        while (purification->mSubstitutions.size() <= i+1)
                            purification->mSubstitutions.push_back(carl::freshIntegerVariable());
                        propagateLinearCaseSplits(*purification, activeDomain, i, false);
                        propagateLogarithmicCaseSplits(*purification, i, true);
                    }
                    propagateFormula(FormulaT(Poly(expansion.mQuotients[i])-Poly(Settings::expansionBase)*Poly(expansion.mQuotients[i+1])-Poly(expansion.mRemainders[i]), carl::Relation::EQ), true);
                    propagateFormula(FormulaT(Poly(expansion.mRemainders[i]), carl::Relation::GEQ), true);
                    propagateFormula(FormulaT(Poly(expansion.mRemainders[i])-Poly(Settings::expansionBase-1), carl::Relation::LEQ), true);
                }
            else if (domain.diameter() <= Settings::maxDomainSize)
            {
                // Switch from logarithmic to linear encoding
                for (Purification *purification : expansion.mPurifications)
                {
                    propagateLogarithmicCaseSplits(*purification, i, false);
                    propagateLinearCaseSplits(*purification, domain, i, true);
                }
                propagateFormula(FormulaT(Poly(expansion.mQuotients[i])-Poly(Settings::expansionBase)*Poly(expansion.mQuotients[i+1])-Poly(expansion.mRemainders[i]), carl::Relation::EQ), false);
                propagateFormula(FormulaT(Poly(expansion.mRemainders[i]), carl::Relation::GEQ), false);
                propagateFormula(FormulaT(Poly(expansion.mRemainders[i])-Poly(Settings::expansionBase-1), carl::Relation::LEQ), false);
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
            
            // Update variable bounds
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
    inline void CSplitModule<Settings>::propagateLinearCaseSplits(const Purification& purification, const RationalInterval& interval, size_t i, bool assert)
    {
        if (!interval.isEmpty())
            for (Rational alpha = interval.lower(); alpha <= interval.upper(); ++alpha)
                propagateFormula(
                    FormulaT(
                        carl::FormulaType::IMPLIES,
                        FormulaT(Poly(purification.mExpansion->mQuotients[i])-Poly(alpha), carl::Relation::EQ),
                        FormulaT(Poly(purification.mSubstitutions[i])-Poly(alpha)*Poly(purification.mReduction->mSubstitutions[0]), carl::Relation::EQ)
                    ),
                    assert
                );
    }
    
    template<class Settings>
    inline void CSplitModule<Settings>::propagateLogarithmicCaseSplits(const Purification& purification, size_t i, bool assert)
    {
        for (Rational alpha = 0; alpha < Settings::expansionBase; ++alpha)
            propagateFormula(
                FormulaT(
                    carl::FormulaType::IMPLIES,
                    FormulaT(Poly(purification.mExpansion->mRemainders[i])-Poly(alpha), carl::Relation::EQ),
                    FormulaT(Poly(purification.mSubstitutions[i])-Poly(Settings::expansionBase)*Poly(purification.mSubstitutions[i+1])-Poly(alpha)*Poly(purification.mReduction->mSubstitutions[0]), carl::Relation::EQ)
                ),
                assert
            );
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
