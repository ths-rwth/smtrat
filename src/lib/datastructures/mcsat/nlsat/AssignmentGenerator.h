#pragma once

#include "../../../Common.h"

#include "Covering.h"
#include "RootIndexer.h"

#include <carl/util/Bitset.h>

#include <boost/optional.hpp>

#include <iostream>
#include <map>
#include <vector>

namespace smtrat {
namespace nlsat {

class AssignmentGenerator {
private:
	using RAN = carl::RealAlgebraicNumber<Rational>;
	std::set<FormulaT> mConstraints;
	std::set<FormulaT> mMVBounds;
	std::vector<std::pair<carl::Variable, FormulaT>> mVariables;
	Model mModel;
	
	boost::optional<ModelValue> mAssignment;
	boost::optional<FormulasT> mConflictingCore;
	boost::optional<FormulaSetT> mInfeasibleSubset;
	bool mIsUnsat;

	bool isUnivariate(const FormulaT& f, carl::Variable v) const {
		carl::Variables vars;
		f.arithmeticVars(vars);
		auto it = vars.find(v);
		if (it == vars.end()) return false;
		vars.erase(it);
		return mModel.contains(vars);
	}
	void setBitsForInterval(carl::Bitset& bits, std::size_t start, std::size_t end) const {
		for (std::size_t i = start; i <= end; i++) bits.set(i);
	}
	bool satisfies(const FormulaT& f, Model& m, carl::Variable v, const RAN& r) const {
		SMTRAT_LOG_TRACE("smtrat.nlsat", f << ", " << m << ", " << v << ", " << r);
		m.assign(v, r);
		SMTRAT_LOG_TRACE("smtrat.nlsat", r);
		auto res = carl::model::evaluate(f, m);
		SMTRAT_LOG_TRACE("smtrat.nlsat", r);
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Evaluating " << f << " -> " << res);
		if (!res.isBool()) std::exit(75);
		assert(res.isBool());
		return res.asBool();
	}
public:
	void pushAssignment(carl::Variable v, const ModelValue& mv, const FormulaT& f) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << v << " = " << mv);
		
		assert(mModel.find(v) == mModel.end());
		mModel.emplace(v, mv);
		mVariables.emplace_back(v, f);
	}
	void popAssignment() { 
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Removing " << mVariables.back().first << " = " << mModel.evaluated(mVariables.back().first));
		assert(!mVariables.empty());
		mModel.erase(mVariables.back().first);
		mVariables.pop_back();
	}
	void pushConstraint(const FormulaT& f) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << f);
		switch (f.getType()) {
			case carl::FormulaType::CONSTRAINT:
				mConstraints.emplace(f);
				break;
			case carl::FormulaType::VARCOMPARE:
				mMVBounds.emplace(f);
				break;
			default:
				SMTRAT_LOG_ERROR("smtrat.nlsat", "Invalid formula type for a constraint: " << f);
				assert(false);
		}
		
	}
	void popConstraint(const FormulaT& f) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Removing " << f);
		switch (f.getType()) {
			case carl::FormulaType::CONSTRAINT:
				mConstraints.erase(f);
				break;
			case carl::FormulaType::VARCOMPARE:
				mMVBounds.erase(f);
				break;
			default:
				SMTRAT_LOG_ERROR("smtrat.nlsat", "Invalid formula type for a constraint: " << f);
				assert(false);
		}
	}
	const Model& getModel() {
		return mModel;
	}
	const auto& getConstraints() const {
		return mConstraints;
	}
	
	const ModelValue& getAssignment() const {
		assert(mAssignment);
		return *mAssignment;
	}
	const FormulasT& getConflictingCore() const {
		assert(mConflictingCore);
		return *mConflictingCore;
	}
	bool isInCore(const FormulaT& f) const {
		assert(mConflictingCore);
		return std::find(mConflictingCore->begin(), mConflictingCore->end(), f) != mConflictingCore->end();
	}
	
	bool hasAssignment(carl::Variable v) {
		mInfeasibleSubset = boost::none;
		mIsUnsat = false;
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Searching for an assignment for " << v);
		RootIndexer ri;
		std::map<FormulaT, std::pair<std::vector<RAN>, FormulaT>> rootMap;
		for (const auto& f: mConstraints) {
			assert(f.getType() == carl::FormulaType::CONSTRAINT);
			if (!isUnivariate(f, v)) continue;
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Evaluating " << f);
			FormulaT fnew(carl::model::substitute(f, mModel));
			std::vector<RAN> list;
			if (fnew.getType() == carl::FormulaType::CONSTRAINT) {
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Real roots of " << fnew.constraint().lhs() << " in " << v);
				const auto& poly = fnew.constraint().lhs();
				auto roots = carl::model::tryRealRoots(poly, v, mModel);
				if (roots) {
					list = *roots;
				} else {
					SMTRAT_LOG_DEBUG("smtrat.nlsat", "Failed to compute roots, or polynomial becomes zero.");
				}
			} else if (fnew.getType() == carl::FormulaType::TRUE) {
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Ignoring " << f << " which simplified to true.");
			} else {
				assert(fnew.getType() == carl::FormulaType::FALSE);
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Direct conflict with " << f << " which simplified to false.");
				const auto& vars = f.variables();
				mConflictingCore = FormulasT();
				mInfeasibleSubset = FormulaSetT();
				for (const auto& v: mVariables) {
					if (vars.find(v.first) == vars.end()) continue;
					//mConflictingCore->emplace_back(v.second);
					mInfeasibleSubset->emplace(v.second);
				}
				mConflictingCore->emplace_back(f);
				mInfeasibleSubset->emplace(f);
				mIsUnsat = true;
				return false;
			}
			ri.add(list);
			rootMap.emplace(f, std::make_pair(std::move(list), fnew));
		}
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Root map: " << rootMap);
		for (const auto& f: mMVBounds) {
			assert(f.getType() == carl::FormulaType::VARCOMPARE);
			if (!isUnivariate(f, v)) continue;
			FormulaT fnew(carl::model::substitute(f, mModel));
			assert(fnew.getType() == carl::FormulaType::VARCOMPARE);
			ModelValue value = fnew.variableComparison().value();
			if (value.isSubstitution()) {
				// Prevent memory error due to deallocation of shared_ptr before copying value from shared_ptr.
				auto res = value.asSubstitution()->evaluate(mModel);
				value = res;
			}
			if (!value.isRational() && !value.isRAN()) continue;
			std::vector<RAN> list;
			if (value.isRational()) list.emplace_back(value.asRational());
			else list.push_back(value.asRAN().changeVariable(v));
			ri.add(list);
			rootMap.emplace(f, std::make_pair(std::move(list), fnew));
		}
		ri.process();
		Covering cover(ri.size() * 2 + 1);
		Model m = mModel;
		for (const auto& c: rootMap) {
			carl::Bitset b;
			const auto& roots = c.second.first;
			const auto& constraint = c.second.second;
			std::size_t last = 0;
			for (const auto& r: roots) {
				std::size_t cur = ri[r];
				SMTRAT_LOG_TRACE("smtrat.nlsat", constraint << " vs " << ri.sampleFrom(2*cur));
				if (!satisfies(constraint, m, v, ri.sampleFrom(2*cur))) {
					// Refutes interval left of this root
					SMTRAT_LOG_TRACE("smtrat.nlsat", constraint << " refutes " << ri.sampleFrom(2*cur) << " -> " << last << ".." << (2*cur));
					setBitsForInterval(b, last, 2*cur);
				}
				SMTRAT_LOG_TRACE("smtrat.nlsat", constraint << " vs " << ri.sampleFrom(2*cur+1));
				SMTRAT_LOG_TRACE("smtrat.nlsat", ri);
				if (!satisfies(constraint, m, v, r)) {
					// Refutes root
					SMTRAT_LOG_TRACE("smtrat.nlsat", constraint << " refutes " << r << " -> " << 2*cur+1);
					setBitsForInterval(b, 2*cur+1, 2*cur+1);
				}
				SMTRAT_LOG_TRACE("smtrat.nlsat", ri);
				last = 2*cur + 2;
			}
			SMTRAT_LOG_TRACE("smtrat.nlsat", constraint << " vs " << ri.sampleFrom(last));
			if (!satisfies(constraint, m, v, ri.sampleFrom(last))) {
				// Refutes interval right of largest root
				SMTRAT_LOG_TRACE("smtrat.nlsat", constraint << " refutes " << ri.sampleFrom(roots.size()*2) << " -> " << last << ".." << (ri.size()*2));
				setBitsForInterval(b, last, ri.size()*2);
			}
			cover.add(c.first, b);
		}
		SMTRAT_LOG_TRACE("smtrat.nlsat", cover);
		if (cover.conflicts()) {
			mConflictingCore = FormulasT();
			cover.buildConflictingCore(*mConflictingCore);
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "No Assignment, built conflicting core " << *mConflictingCore << " under model " << mModel);
			return false;
		} else {
			mAssignment = ri.sampleFrom(cover.satisfyingInterval());
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Assignment: " << v << " = " << *mAssignment);
			assert(mAssignment->isRAN());
			if (mAssignment->asRAN().isNumeric()) {
				mAssignment = mAssignment->asRAN().value();
			}
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Assignment: " << v << " = " << *mAssignment);
			return true;
		}
	}
	
	bool hasInfeasibleSubset() const {
		return bool(mInfeasibleSubset);
	}
	bool isUnsat() const {
		return mIsUnsat;
	}
	const FormulaSetT& getInfeasibleSubset() const {
		return *mInfeasibleSubset;
	}
};

}
}
