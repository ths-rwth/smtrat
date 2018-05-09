#pragma once

#include "../common.h"
#include "../Bookkeeping.h"

namespace smtrat {
namespace mcsat {
namespace fm {

struct ConflictGenerator {
	using Bound = std::tuple<ConstraintT,Poly,Rational>;
private:
	std::vector<Bound> mLower;
	std::vector<Bound> mUpper;
	std::map<Rational,ConstraintT> mInequalities;
	std::pair<std::size_t,std::size_t> mNext = std::make_pair(0, 0);

public:
	ConflictGenerator(const std::vector<ConstraintT>& bounds, const Model& m, carl::Variable v) {
		for (const auto& b: bounds) {
			assert(b.coefficient(v, 1).isConstant());
			auto coeff = b.coefficient(v, 1).constantPart();
			assert(!carl::isZero(coeff));
			auto poly = (v*coeff - b.lhs()) / coeff;
			
			auto res = carl::model::evaluate(poly, m);
			assert(res.isRational());
			
			switch (b.relation()) {
				case carl::Relation::LESS:
				case carl::Relation::LEQ:
					if (coeff > 0) {
						mUpper.emplace_back(b, poly, res.asRational());
					} else {
						mLower.emplace_back(b, poly, res.asRational());
					}
					break;
				case carl::Relation::EQ:
					mLower.emplace_back(b, poly, res.asRational());
					mUpper.emplace_back(b, poly, res.asRational());
					break;
				case carl::Relation::NEQ:
					mInequalities.emplace(res.asRational(), b);
					break;
				case carl::Relation::GEQ:
				case carl::Relation::GREATER:
					if (coeff > 0) {
						mLower.emplace_back(b, poly, res.asRational());
					} else {
						mUpper.emplace_back(b, poly, res.asRational());
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
	
	boost::optional<ConstraintT> operator()() {
		assert(hasNext());
		
		const Bound& lower = mLower[mNext.first];
		const Bound& upper = mUpper[mNext.second];
		bool strict = carl::isStrict(std::get<0>(lower).relation()) || carl::isStrict(std::get<0>(upper).relation());
		const auto& lp = std::get<1>(lower);
		const auto& up = std::get<1>(upper);
		const auto& lr = std::get<2>(lower);
		const auto& ur = std::get<2>(upper);
		
		if (lr < ur) {
			return boost::none;
		}
		if (lr == ur && !strict) {
			if (mInequalities.find(lr) != mInequalities.end()) {
				// Only allows for a point solution which is excluded by an inequality.
				strict = true;
			} else {
				return boost::none;
			}
		}
		
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "-> " << std::get<1>(lower) << " vs. " << std::get<1>(upper));
		
		return ConstraintT(lp - up, strict ? carl::Relation::LESS : carl::Relation::LEQ);
	}
};

struct Explanation {
	boost::optional<FormulaT> operator()(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason, const FormulaT& implication) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "With " << reason << " explain " << implication);
		
		std::vector<ConstraintT> bounds;
		for (const auto& b: reason) {
			assert(b.getType() == carl::FormulaType::CONSTRAINT);
			bounds.emplace_back(b.constraint());
		}
		ConflictGenerator cg(bounds, data.model(), var);
		
		while (cg.hasNext()) {
			auto res = cg();
			if (res) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Found conflict " << *res);
				FormulasT expl;
				for (const auto& r: reason) expl.emplace_back(r.negated());
				expl.emplace_back(*res);
				return FormulaT(carl::FormulaType::OR, std::move(expl));
			}
			cg.next();
		}
		
		return boost::none;
	}
};

}
}
}
