#pragma once

#include "../common.h"
#include "../Bookkeeping.h"

namespace smtrat {
namespace mcsat {
namespace fm {

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
	using Bound = std::tuple<ConstraintT,Poly,Poly,Rational,bool>;
private:
	std::vector<Bound> mLower;
	std::vector<Bound> mUpper;
	std::map<Rational,ConstraintT> mInequalities;
	std::pair<std::size_t,std::size_t> mNext = std::make_pair(0, 0);

public:
	ConflictGenerator(const std::vector<ConstraintT>& bounds, const Model& m, carl::Variable v) {
		for (const auto& b: bounds) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Processing bound " << b);
			if (b.varInfo(v).maxDegree() > 1) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because " << v << " occurs nonlinearly");
				continue;
			}
			auto p = b.coefficient(v, 1);
			if (p.isZero()) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because it does not contain " << v);
				continue;
			}
			
			auto evalp = carl::model::evaluate(p, m);
			if (!evalp.isRational()) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because " << p << " did not evaluate to a rational");
				continue;
			}
			assert(evalp.isRational());
			if (carl::isZero(evalp.asRational())) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because it does not contain " << v << " after we evaluate it");
				continue;
			}
			bool negated = evalp.asRational() < 0;
			
			auto q = p * v - b.lhs();
			auto evalq = carl::model::evaluate(q, m);
			if (!evalq.isRational()) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because " << q << " did not evaluate to a rational");
				continue;
			}
			assert(evalq.isRational());
			Rational r = evalq.asRational() / evalp.asRational();
			
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Considering bound " << b << " for " << v);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Decomposed into " << p << " * " << v << " + " << q << ", " << v << " ~ " << r);
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
					break;
				case carl::Relation::NEQ:
					mInequalities.emplace(r, b);
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
	}
	
	bool hasNext() const {
		return mNext.first < mLower.size() && mNext.second < mUpper.size();
	}
	void next() {
		++mNext.first;
		if (mNext.first == mLower.size()) {
			mNext.first = 0;
			++mNext.second;
		}
	}
	
	boost::optional<FormulasT> operator()() {
		if (!hasNext()) return boost::none;
		assert(hasNext());
		
		const Bound& lower = mLower[mNext.first];
		const Bound& upper = mUpper[mNext.second];
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Combining " << lower << " and " << upper);
		bool strict = carl::isStrict(std::get<0>(lower).relation()) || carl::isStrict(std::get<0>(upper).relation());
		const auto& lp = std::get<1>(lower);
		const auto& up = std::get<1>(upper);
		const auto& lq = std::get<2>(lower);
		const auto& uq = std::get<2>(upper);
		const auto& lr = std::get<3>(lower);
		const auto& ur = std::get<3>(upper);
		const auto& lneg = std::get<4>(lower);
		const auto& uneg = std::get<4>(upper);
		
		if (lr < ur) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Not in conflict");
			return boost::none;
		}
		FormulasT res;
		res.emplace_back(std::get<0>(lower).negation());
		res.emplace_back(std::get<0>(upper).negation());
		if (lr == ur && !strict) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Not in conflict");
			return boost::none;
			auto it = mInequalities.find(lr);
			if (it != mInequalities.end()) {
				// Only allows for a point solution which is excluded by an inequality.
				strict = true;
				res.emplace_back(it->second.negation());
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "In conflict due to inequality " << it->second);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Not in conflict");
				return boost::none;
			}
		}
		
		carl::Relation rel = (lneg xor uneg) ? (strict ? carl::Relation::GREATER : carl::Relation::GEQ) : (strict ? carl::Relation::LESS : carl::Relation::LEQ);
		
		res.emplace_back(ConstraintT(lq*up - uq*lp, rel));
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Conflict: " << lq << " * " << up << " " << rel << " " << uq << " * " << lp);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "-> " << res.back());
		
		res.emplace_back(ConstraintT(lp, lneg ? carl::Relation::LESS : carl::Relation::GREATER).negation());
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Side condition on " << lp << ": " << res.back().negated());
		res.emplace_back(ConstraintT(up, uneg ? carl::Relation::LESS : carl::Relation::GREATER).negation());
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Side condition on " << up << ": " << res.back().negated());
		return res;
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
		
		while (cg.hasNext()) {
			auto res = cg();
			if (res) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Found conflict " << *res);
				return FormulaT(carl::FormulaType::OR, std::move(*res));
			}
			cg.next();
		}
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Did not find a conflict");
		
		return boost::none;
	}
};

}
}
}
