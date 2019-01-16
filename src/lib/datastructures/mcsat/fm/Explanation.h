#pragma once

#include "../common.h"

#include "FMStatistics.h"

#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat {
namespace mcsat {
namespace fm {

using carl::operator<<;

inline bool isSubset(const carl::Variables& subset, const carl::Variables& superset) {
	return std::includes(superset.begin(), superset.end(), subset.begin(), subset.end());
}

struct Bound {
	ConstraintT constr;
	Poly p;
	Poly q;
	Rational r;
	bool neg;
	Bound(ConstraintT constr, Poly p, Poly q, Rational r, bool neg) : constr(constr), p(p), q(q), r(r), neg(neg) {}
	friend ostream& operator<<(ostream& os, const Bound& dt);  
};

inline ostream& operator<<(ostream& os, const Bound& b) {
	os << "(" << b.constr << ", " << b.p << ", " << b.q << ", " << b.r << ", " << b.neg << ")";  
	return os;  
}

template<class Comparator>
struct ConflictGenerator {
	/**
	 * Preprocessing of constraints:
	 * 
	 * The input is a constraint c: p*x~q which can be used as a bound on x with p,q multivariate polynomials.
	 * If x only occurs linearly in c, this decomposition is possible.
	 * If p is zero, then c is conflicting iff !(0~q). If this is the case, we can return !c && p=0 -> 0~q as explanation.
	 * Otherwise, we evaluate c over the partial model and obtain x~r, where r is a rational.
	 * To properly perform the elimination step detailed below, we additionally store whether p is negative over the current assignment as a Boolean.
	 *
	 * We store (c,p,q,r,n) for each bound.
	 * 
	 * 
	 * FM elimination:
	 *
	 * Given a lower bound l and an upper bound u, the elimination is as follows:
	 *   Conflict if l.r >= u.r (or strict, if both relations from c are weak)
	 *   l.q * u.p < u.q * l.p
	 *
	 * If exactly one of u.p and l.p was found to be negative, the relation has to be inverted.
	 * If u.p or l.p are not constants, we additionally have to add a literal stating that their sign does not change.
	 * 
	 * For all bounds involved, we add b.p < 0 resp. b.p > 0 as side condition to the explanation.
	 * 
	 * 
	 * Handling of "not equal":
	 * 
	 * For linear arithmetic, a bound i belonging to a constraint with relation != can be in conflict with
	 * * a bound e for a constraint with = iff i.r == e.r, then we return i.c && e.c -> i.q * e.p != e.q * i.p
	 * * two bounds l, u with >= resp. <= as relation and i.r == l.r == u.r, then we return i.c && l.c && u.c && (l.q * u.p = u.q * l.p) -> l.q * i.p != i.q * l.p
	 * 
	 * For all bounds b involved, we add b.p != 0 as side condition to the explanation. 
	 */


	#define mcsat_yield(callback, result) if (callback(std::move(result))) { return; }

	
private:
	const std::vector<ConstraintT>& mBounds;
	const Model& mModel;
	carl::Variable mVariable;

	Comparator comparator;

public:
	ConflictGenerator(const std::vector<ConstraintT>& bounds, const Model& m, carl::Variable v) : mBounds(bounds), mModel(m), mVariable(v) {}

private: 
	ConstraintT sideCondition(const Bound& b) {
		ConstraintT res = ConstraintT(b.p, carl::Relation::NEQ);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Side condition on " << b.p << ": " << res);
		return res;
	}

	ConstraintT sideConditionLoUp(const Bound& b) {
		ConstraintT res = ConstraintT(b.p, b.neg ? carl::Relation::LESS : carl::Relation::GREATER);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Side condition on " << b.p << ": " << res);
		return res;
	}

	FormulasT conflictLowerAndUpperBound(const Bound& lower, const Bound& upper) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Lower bound " << lower << " in conflict with upper bound " << upper);
		bool strict = carl::isStrict(lower.constr.relation()) || carl::isStrict(upper.constr.relation());
		carl::Relation rel = (lower.neg xor upper.neg) ? (strict ? carl::Relation::GREATER : carl::Relation::GEQ) : (strict ? carl::Relation::LESS : carl::Relation::LEQ);
		FormulasT res;
		res.emplace_back(lower.constr.negation());
		res.emplace_back(upper.constr.negation());
		res.emplace_back(ConstraintT(lower.q*upper.p - upper.q*lower.p, rel));
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Conflict: " << lower.q << " * " << upper.p << " " << rel << " " << upper.q << " * " << lower.p);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "-> " << res.back());
		res.emplace_back(sideConditionLoUp(lower).negation());
		res.emplace_back(sideConditionLoUp(upper).negation());
		return res;
	}

	FormulasT conflictEqualityAndInequality(const Bound& eq, const Bound& ineq) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Equality " << eq << " in conflict with inqequality " << ineq);
		FormulasT expl;
		expl.emplace_back(ineq.constr.negation());
		expl.emplace_back(eq.constr.negation());
		expl.emplace_back(ConstraintT(eq.q*ineq.p - ineq.q*eq.p, carl::Relation::NEQ));
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Explanation: " << expl[0].negated() << " && " << expl[1].negated() << " -> " << expl[2]);
		expl.emplace_back(sideCondition(eq).negation());
		expl.emplace_back(sideCondition(ineq).negation());
		return expl;
	}

	FormulasT conflictInequalitiesAndInequality(const Bound& lower, const Bound& upper, const Bound& ineq) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Lower bound " << lower << " and upper bound " << upper << " in conflict with inqequality " << ineq);
		FormulasT expl;
		expl.emplace_back(ineq.constr.negation());
		expl.emplace_back(lower.constr.negation());
		expl.emplace_back(upper.constr.negation());
		expl.emplace_back(ConstraintT(lower.q*upper.p - upper.q*lower.p, carl::Relation::EQ).negation());
		expl.emplace_back(ConstraintT(lower.q*ineq.p - ineq.q*lower.p, carl::Relation::NEQ));
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Explanation: " << expl[0].negated() << " && " << expl[1].negated() << " && " << expl[2].negated() << " && " << expl[3].negated() << " -> " << expl[4]);
		expl.emplace_back(sideCondition(ineq).negation());
		expl.emplace_back(sideConditionLoUp(lower).negation());
		expl.emplace_back(sideConditionLoUp(upper).negation()); // TODO move to struct member
		return expl;
	}

public:

	template<typename Callback>
	void generateExplanation(Callback&& callback) {
		std::vector<Bound> mLower;
		std::vector<Bound> mUpper;
		std::multimap<Rational, Bound> mInequalities;
		std::vector<Bound> mEqualities;
		std::vector<std::pair<Bound, Bound>> mBoundPair;
		
		// initialize bounds
		for (const auto& b: mBounds) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Processing bound " << b);

			if (!b.hasVariable(mVariable)) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because it does not contain " << mVariable);
				continue;
			}

			if (b.varInfo(mVariable).maxDegree() > 1) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because " << mVariable << " occurs nonlinearly");
				continue;
			}
			auto p = b.coefficient(mVariable, 1);
			if (carl::isZero(p)) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because it does not contain " << mVariable);
				continue;
			}
			
			auto evalp = carl::model::evaluate(p, mModel);
			if (!evalp.isRational()) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because " << p << " did not evaluate to a rational");
				continue;
			}
			assert(evalp.isRational());

			auto q = p * mVariable - b.lhs();
			auto evalq = carl::model::evaluate(q, mModel);
			if (!evalq.isRational()) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because " << q << " did not evaluate to a rational");
				continue;
			}
			assert(evalq.isRational());

			if (carl::isZero(evalp.asRational())) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because it does not contain " << mVariable << " after we evaluate it");

				if (!carl::evaluate(Rational(0), b.relation(), evalq.asRational())) {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Bound " << b << " unsat because p is zero and q does not comply");
					FormulasT expl;
					expl.emplace_back(b.negation());
					expl.emplace_back(ConstraintT(p, carl::Relation::EQ).negation());
					expl.emplace_back(ConstraintT(-q, b.relation()));

					SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Explanation: " << expl[0].negated() << " && " << expl[1].negated() << " -> " << expl[2]);
					mcsat_yield(callback, expl);
				}

				continue;
			}
			bool negated = evalp.asRational() < 0;
			
			Rational r = evalq.asRational() / evalp.asRational();
			
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Considering bound " << b << " for " << mVariable);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Decomposed into " << p << " * " << mVariable << " ~ " << q << ", " << mVariable << " ~ " << r);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Coefficient is " << evalp.asRational());
			
			switch (b.relation()) {
				case carl::Relation::LESS:
				case carl::Relation::LEQ:
					if (negated) {
						mLower.emplace_back(b, p, q, r, negated);
					} else {
						mUpper.emplace_back(b, p, q, r, negated);
					}
					break;
				case carl::Relation::EQ:
					mLower.emplace_back(b, p, q, r, negated);
					mUpper.emplace_back(b, p, q, r, negated);
					mEqualities.emplace_back(b, p, q, r, negated);
					break;
				case carl::Relation::NEQ:
					mInequalities.emplace(r, Bound(b, p, q, r, negated));
					break;
				case carl::Relation::GEQ:
				case carl::Relation::GREATER:
					if (negated) {
						mUpper.emplace_back(b, p, q, r, negated);
					} else {
						mLower.emplace_back(b, p, q, r, negated);
					}
					break;
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Lower: " << mLower);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Upper: " << mUpper);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Inequ: " << mInequalities);
	
		// look for FM constraints
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Looking for conflicts between lower and upper bounds");

		std::sort(mLower.begin(), mLower.end(), comparator);
		if (comparator.symmetric) {
			std::sort(mUpper.rbegin(), mUpper.rend(), comparator);
		}
		else {
			std::sort(mUpper.begin(), mUpper.end(), comparator);
		}

		for (const Bound& lower : mLower) {
			for (const Bound& upper : mUpper) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Combining " << lower << " and " << upper);
				bool strict = carl::isStrict(lower.constr.relation()) || carl::isStrict(upper.constr.relation());
				
				if (lower.r < upper.r) {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Not in conflict");
					continue;
				}
				
				if (lower.r == upper.r && !strict) {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Not in conflict");
					mBoundPair.push_back(std::make_pair(lower, upper));
					continue;
				}

				mcsat_yield(callback, conflictLowerAndUpperBound(lower, upper));
			}
		}

		// handle inequalities
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Looking for conflicts with inequalities");

		for (const auto& eq : mEqualities) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Considering equality " << eq.constr);
			auto it = mInequalities.find(eq.r);
			if (it != mInequalities.end()) {
				mcsat_yield(callback, conflictEqualityAndInequality(eq, it->second));
			}
		}

		for (const auto& bounds : mBoundPair) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Considering lower bound " << bounds.first << " and upper bound " << bounds.second);
			auto it = mInequalities.find(bounds.first.r);
			if (it != mInequalities.end()) {
				mcsat_yield(callback, conflictInequalitiesAndInequality(bounds.first, bounds.second, it->second));
			}
		}
	}
};

/**
 * Does not order anything.
 */
struct DefaultComparator {
	bool symmetric = false;

	bool operator()(const Bound&, const Bound&) const {
		return false;
	}
};

/**
 * This heuristic chooses the explanation excluding the largest interval. 
 */
struct MaxSizeComparator {
	bool symmetric = true;

	bool operator()(const Bound& b1, const Bound& b2) const {
		return b1.r < b2.r;
	}
};

/**
 * This heuristic chooses the explanation excluding the smallest interval. 
 */
struct MinSizeComparator {
	bool symmetric = true;

	bool operator()(const Bound& b1, const Bound& b2) const {
		return b1.r > b2.r;
	}
};

/**
 * This heuristic tries to minimize the number of variables occuring in the explanation.
 * It is a 2-approximation to the lowest possible number of variables in an explanation.
 */
struct MinVarCountComparator {
	bool symmetric = false;

	bool operator()(const Bound& b1, const Bound& b2) const {
		return b1.constr.variables().size() < b2.constr.variables().size();
	}
};


struct DefaultSettings {
	static constexpr bool use_all_constraints = false;
};
struct IgnoreCoreSettings {
	static constexpr bool use_all_constraints = true;
};

template<class Settings>
struct Explanation {

#ifdef SMTRAT_DEVOPTION_Statistics
	mutable FMStatistics mStatistics;
    Explanation() : mStatistics("mcsat-explanation-fm") {}
#endif

	boost::optional<mcsat::Explanation> operator()(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason) const {
		#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.explanationCalled();
		#endif

		std::vector<ConstraintT> bounds;

		if (!Settings::use_all_constraints) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Explain conflict " <<  reason);
		
			for (const auto& b : reason) {
				if (b.getType() != carl::FormulaType::CONSTRAINT) {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding non-constraint bound " << b);
					continue;
				}
				assert(b.getType() == carl::FormulaType::CONSTRAINT);
				bounds.emplace_back(b.constraint());
			}
		} else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Explain conflict " <<  data.constraints());
		
			for (const auto& b : data.constraints()) {
				carl::Variables allowedVars;
				auto curVar = std::find(variableOrdering.begin(), variableOrdering.end(), var); 
				assert(curVar != variableOrdering.end());
				allowedVars.insert(variableOrdering.begin(), curVar+1);
				if (!isSubset(b.variables(), allowedVars)) {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding non-univariate bound " << b);
					continue;
				}
				assert(b.getType() == carl::FormulaType::CONSTRAINT);
				bounds.emplace_back(b.constraint());
			}
		}

		boost::optional<FormulasT> res = boost::none;
		ConflictGenerator<DefaultComparator>(bounds, data.model(), var).generateExplanation([&](FormulasT expl) -> bool {
			res = expl;
			return true; // stop searching for conflicts after first conflict has been found
		});

		if (res) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Found conflict " << *res);
			#ifdef SMTRAT_DEVOPTION_Statistics
			mStatistics.explanationSuccess();
			#endif
			return mcsat::Explanation(FormulaT(carl::FormulaType::OR, std::move(*res)));
		}
		else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Did not find a conflict");
			return boost::none;
		}
	}
};

}
}
}
