#pragma once

#include "../common.h"
#include "../Bookkeeping.h"

namespace smtrat {
namespace mcsat {
namespace fm {

inline bool compare(Rational r1, Rational r2, carl::Relation rel) {
	switch (rel) {
		case carl::Relation::LESS:
			return r1 < r2;
			break;
		case carl::Relation::LEQ:
			return r1 <= r2;
			break;
		case carl::Relation::GEQ:
			return r1 >= r2;
			break;
		case carl::Relation::GREATER:
			return r1 > r2;
			break;
		case carl::Relation::EQ:
			return r1 == r2;
			break;
		case carl::Relation::NEQ:
			return r1 != r2;
			break;
	}
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

inline ostream& operator<<(ostream& os, const Bound& b)  {  
	os << "(" << b.constr << ", " << b.p << ", " << b.q << ", " << b.r << ", " << b.neg << ")";  
	return os;  
}  

inline std::ostream& operator<< (std::ostream& out, const std::vector<Bound>& v) {
    out << '[';
    for (const auto& b : v) {
		out << b << ", ";
	}
    out << "\b\b]";
  	return out;
}

inline std::ostream& operator<< (std::ostream& out, const std::multimap<Rational, Bound>& v) {
    out << '[';
    for (const auto& b : v) {
		out << b.second << ", ";
	}
    out << "\b\b]";
  	return out;
}

struct ConflictGenerator {
	/**
	 * The input is a constraint c: p*x~q which can be used as a bound on x with p,q multivariate polynomials.
	 * If x only occurs linearly in c, this decomposition is possible.
	 * We evaluate c over the partial model and obtain x~r, where r is a rational.
	 * To properly perform the elimination step detailed below, we additionally store whether p is negative over the current assignment as a Boolean.
	 *
	 * We store (c,p,q,r,n) for each bound.
	 *
	 * Given a lower bound l and an upper bound u, the elimination is as follows:
	 *   Conflict if l.r >= u.r (or strict, if both relations from c are weak)
	 *   l.q * u.p < u.q * l.p
	 *
	 * If exactly one of u.p and l.p was found to be negative, the relation has to be inverted.
	 * If u.p or l.p are not constants, we additionally have to add a literal stating that their sign does not change.
	 */

	//using Bound = std::tuple<ConstraintT,Poly,Poly,Rational,bool>;

	
private:
	const std::vector<ConstraintT>& mBounds;
	const Model& mModel;
	carl::Variable mVariable;

	std::vector<Bound> mLower;
	std::vector<Bound> mUpper;
	std::multimap<Rational, Bound> mInequalities;
	std::vector<Bound> mEqualities;
	std::vector<std::pair<Bound, Bound>> mBoundPair;


public:
	ConflictGenerator(const std::vector<ConstraintT>& bounds, const Model& m, carl::Variable v) : mBounds(bounds), mModel(m), mVariable(v) {}

	ConstraintT sideCondition(const Bound& b) {
		ConstraintT res = ConstraintT(b.p, carl::Relation::NEQ);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Side condition on " << b.p << ": " << res);
		return std::move(res);
	}

	ConstraintT sideConditionLo(const Bound& b) {
		ConstraintT res = ConstraintT(b.p, b.neg ? carl::Relation::LESS : carl::Relation::GREATER);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Side condition on " << b.p << ": " << res);
		return std::move(res);
	}

	ConstraintT sideConditionUp(const Bound& b) {
		ConstraintT res = ConstraintT(b.p, b.neg ? carl::Relation::LESS : carl::Relation::GREATER);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Side condition on " << b.p << ": " << res);
		return std::move(res);
	}

	FormulasT conflictLowerAndUpperBound(const Bound& lower, const Bound& upper, bool strict) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Lower bound " << lower << " in conflict with upper bound " << upper);
		carl::Relation rel = (lower.neg xor upper.neg) ? (strict ? carl::Relation::GREATER : carl::Relation::GEQ) : (strict ? carl::Relation::LESS : carl::Relation::LEQ);
		FormulasT res;
		res.emplace_back(lower.constr.negation());
		res.emplace_back(upper.constr.negation());
		res.emplace_back(ConstraintT(lower.q*upper.p - upper.q*lower.p, rel));
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Conflict: " << lower.q << " * " << upper.p << " " << rel << " " << upper.q << " * " << lower.p);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "-> " << res.back());
		res.emplace_back(sideConditionLo(lower).negation());
		res.emplace_back(sideConditionUp(upper).negation());
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
		expl.emplace_back(sideConditionLo(lower).negation());
		expl.emplace_back(sideConditionUp(upper).negation());
		return expl;
	}

	boost::optional<FormulasT> initBounds() {
		for (const auto& b: mBounds) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Processing bound " << b);
			if (b.varInfo(mVariable).maxDegree() > 1) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because " << mVariable << " occurs nonlinearly");
				continue;
			}
			auto p = b.coefficient(mVariable, 1);
			if (p.isZero()) {
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

				if (!compare(Rational(0), evalq.asRational(), b.relation())) {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Bound " << b << " unsat because p is zero and q does not comply");
					FormulasT expl;
					expl.emplace_back(b.negation());
					expl.emplace_back(ConstraintT(p, carl::Relation::EQ).negation());
					expl.emplace_back(ConstraintT(-q, b.relation()));
					SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Explanation: " << expl[0].negated() << " && " << expl[1].negated() << " -> " << expl[2]);
					return expl;
				}

				continue;
			}
			bool negated = evalp.asRational() < 0;
			
			Rational r = evalq.asRational() / evalp.asRational();
			
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Considering bound " << b << " for " << mVariable);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Decomposed into " << p << " * " << mVariable << " + " << q << ", " << mVariable << " ~ " << r);
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

		return boost::none;
	}

	boost::optional<FormulasT> handleFM() {
		// TODO sort lower and upper bounds according to a heuristic
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Looking for conflicts between lower and upper bounds");
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

				return conflictLowerAndUpperBound(lower, upper, strict);
			}
		}
		return boost::none;
	}

	boost::optional<FormulasT> handleInequalities() { 
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Looking for conflicts with inequalities");

		for (const auto& eq : mEqualities) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Considering equality " << eq.constr);
			auto it = mInequalities.find(eq.r);
			if (it != mInequalities.end()) {
				return conflictEqualityAndInequality(eq, it->second);
			}
		}

		for (const auto& bounds : mBoundPair) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Considering lower bound " << bounds.first << " and upper bound " << bounds.second);
			auto it = mInequalities.find(bounds.first.r);
			if (it != mInequalities.end()) {
				return conflictInequalitiesAndInequality(bounds.first, bounds.second, it->second);
			}
		}

		return boost::none;
	}

	boost::optional<FormulasT> generateExplanation() {
		// TODO ugly, but I did not found anything to chain boost::optional...
		auto res = initBounds();
		if (res != boost::none) {
			return res;
		}
		res = handleFM();
		if (res != boost::none) {
			return res;
		}
		return handleInequalities();
	}
};

struct Explanation {
	boost::optional<FormulaT> operator()(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason, const FormulaT& implication) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "With " << reason << " explain " << implication);
		
		std::vector<ConstraintT> bounds;
		for (const auto& b: reason) {
			if (b.getType() != carl::FormulaType::CONSTRAINT) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding non-constraint bound " << b);
				continue;
			}
			assert(b.getType() == carl::FormulaType::CONSTRAINT);
			bounds.emplace_back(b.constraint());
		}
		ConflictGenerator cg(bounds, data.model(), var);
		auto res = cg.generateExplanation();
		if (res) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Found conflict " << *res);
			return FormulaT(carl::FormulaType::OR, std::move(*res));
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
