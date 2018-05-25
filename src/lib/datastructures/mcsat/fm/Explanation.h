#pragma once

#include "../common.h"
#include "../Bookkeeping.h"

namespace smtrat {
namespace mcsat {
namespace fm {

struct ConflictGenerator {
	/**
	 * The input is a constraint c: p*x+q~0 which can be used as a bound on x with p,q multivariate polynomials.
	 * If x only occurs linearly in c, this decomposition is possible.
	 * We evaluate c over the partial model and obtain x~r, where r is a rational.
	 *
	 * We store (c,p,q,r) for each bound.
	 *
	 * Given a lower bound l and an upper bound u, the elimination is as follows:
	 *   Conflict if l.r >= u.r (or strict, if both relations from c are weak)
	 *   l.q * u.p < u.q * l.p
	 */
	using Bound = std::tuple<ConstraintT,Poly,Poly,Rational>;
private:
	std::vector<Bound> mLower;
	std::vector<Bound> mUpper;
	std::map<Rational,ConstraintT> mInequalities;
	std::pair<std::size_t,std::size_t> mNext = std::make_pair(0, 0);

public:
	ConflictGenerator(const std::vector<ConstraintT>& bounds, const Model& m, carl::Variable v) {
		for (const auto& b: bounds) {
			if (b.varInfo(v).maxDegree() > 1) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because " << v << " occurs nonlinearly");
				continue;
			}
			auto p = b.coefficient(v, 1);
			if (p.isZero()) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding bound " << b << " because it does not contain " << v);
				continue;
			}
			auto q = b.lhs() - p * v;
			
			auto evalp = carl::model::evaluate(p, m);
			auto evalq = carl::model::evaluate(q, m);
			assert(evalp.isRational() && evalq.isRational());
			Rational r = - evalq.asRational() / evalp.asRational();
			
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Considering bound " << b << " for " << v);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Decomposed into " << p << " * " << v << " + " << q << ", " << v << " ~ " << r);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Coefficient is " << evalp.asRational());
			
			switch (b.relation()) {
				case carl::Relation::LESS:
				case carl::Relation::LEQ:
					if (evalp.asRational() > 0) {
						mUpper.emplace_back(b, p, q, r);
					} else {
						mLower.emplace_back(b, p, q, r);
					}
					break;
				case carl::Relation::EQ:
					mLower.emplace_back(b, p, q, r);
					mUpper.emplace_back(b, p, q, r);
					break;
				case carl::Relation::NEQ:
					mInequalities.emplace(r, b);
					break;
				case carl::Relation::GEQ:
				case carl::Relation::GREATER:
					if (evalp.asRational() > 0) {
						mLower.emplace_back(b, p, q, r);
					} else {
						mUpper.emplace_back(b, p, q, r);
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
		
		if (lr < ur) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Not in conflict");
			return boost::none;
		}
		FormulasT res;
		if (lr == ur && !strict) {
			auto it = mInequalities.find(lr);
			if (it != mInequalities.end()) {
				// Only allows for a point solution which is excluded by an inequality.
				strict = true;
				res.emplace_back(it->second);
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "In conflict due to inequality " << it->second);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Not in conflict");
				return boost::none;
			}
		}
		
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "-> " << lp << " * " << uq << " " << (strict ? carl::Relation::LESS : carl::Relation::LEQ) << " " << up << " * " << lq);
		
		res.emplace_back(ConstraintT(lq*up - uq*lp, strict ? carl::Relation::LESS : carl::Relation::LEQ));
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
				for (const auto& r: reason) res->emplace_back(r.negated());
				return FormulaT(carl::FormulaType::OR, std::move(*res));
			}
			cg.next();
		}
		
		return boost::none;
	}
};

}
}
}
