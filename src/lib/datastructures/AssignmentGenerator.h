#pragma once

#include "../Common.h"

#include <carl/util/Bitset.h>
#include <carl/util/Covering.h>

#include <boost/optional.hpp>

#include <iostream>
#include <map>
#include <vector>

namespace smtrat {

class RootIndexer {
public:
	using RAN = carl::RealAlgebraicNumber<Rational>;
private:
	std::vector<RAN> mRoots;
	std::map<RAN, std::size_t> mMap;
	std::vector<RAN> mSamples;
public:	
	void add(const std::vector<RAN>& list) {
		mRoots.insert(mRoots.end(), list.begin(), list.end());
	}
	void process() {
		std::sort(mRoots.begin(), mRoots.end());
		mRoots.erase(std::unique(mRoots.begin(), mRoots.end()), mRoots.end());
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Roots: " << mRoots);
		for (std::size_t i = 0; i < mRoots.size(); i++) {
			mMap.emplace(mRoots[i], i);
		}
		mSamples.reserve(mRoots.size() + 1);
		for (std::size_t n = 0; n < mRoots.size(); n++) {
			if (n == 0) mSamples.emplace_back(RAN::sampleBelow(mRoots.front()));
			else mSamples.emplace_back(RAN::sampleBetween(mRoots[n-1], mRoots[n]));
			mSamples.emplace_back(mRoots[n]);
		}
		mSamples.emplace_back(RAN::sampleAbove(mRoots.back()));
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Samples: " << mSamples);
	}
	std::size_t size() const {
		return mRoots.size();
	}
	std::size_t operator[](const RAN& ran) const {
		auto it = mMap.find(ran);
		assert(it != mMap.end());
		return it->second;
	}
	const RAN& operator[](std::size_t n) const {
		assert(n < mRoots.size());
		return mRoots[n];
	}
	const RAN& sampleFrom(std::size_t n) const {
		return mSamples[n];
	}
};
std::ostream& operator<<(std::ostream& os, const RootIndexer& ri) {
	os << "Roots:" << std::endl;
	for (std::size_t i = 0; i < ri.size(); i++) {
		os << "\t" << i << " <-> " << ri[i] << std::endl;
	}
	os << "Samples:" << std::endl;
	for (std::size_t i = 0; i < ri.size()*2+1; i++) {
		os << "\t" << ri.sampleFrom(i) << std::endl;;
	}
	return os;
}

/**
 * Semantics:
 * The space is divided into a number of intervals: (-oo,a)[a,a](a,b)[b,b](b,oo)
 * A bit is set if the constraints refutes the corresponding interval
 */
using Covering = carl::Covering<ConstraintT>;

class AssignmentGenerator {
private:
	using RAN = carl::RealAlgebraicNumber<Rational>;
	std::set<ConstraintT> mConstraints;
	std::vector<carl::Variable> mVariables;
	Model mModel;
	
	boost::optional<ModelValue> mAssignment;
	boost::optional<std::vector<ConstraintT>> mConflictingCore;

	bool isUnivariate(const ConstraintT& c, carl::Variable v) const {
		auto vars = c.variables();
		auto it = vars.find(v);
		if (it == vars.end()) return false;
		vars.erase(it);
		return mModel.contains(vars);
	}
	void setBitsForInterval(carl::Bitset& bits, std::size_t start, std::size_t end) const {
		for (std::size_t i = start; i <= end; i++) bits.set(i);
	}
	bool satisfies(const ConstraintT& c, Model& m, carl::Variable v, const RAN& r) const {
		m.assign(v, r);
		auto res = carl::model::evaluate(c, m);
		assert(res.isBool());
		return res.asBool();
	}
public:
	void pushAssignment(carl::Variable v, const ModelValue& mv) {
		assert(mModel.find(v) == mModel.end());
		mModel.emplace(v, mv);
		mVariables.push_back(v);
	}
	void popAssignment() {
		assert(!mVariables.empty());
		mModel.erase(mVariables.back());
		mVariables.pop_back();
	}
	void pushConstraint(const ConstraintT& c) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << c);
		mConstraints.emplace(c);
	}
	void popConstraint(const ConstraintT& c) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Removing " << c);
		mConstraints.erase(c);
	}
	const Model& getModel() {
		return mModel;
	}
	
	const ModelValue& getAssignment() const {
		assert(mAssignment);
		return *mAssignment;
	}
	const std::vector<ConstraintT>& getConflictingCore() const {
		assert(mConflictingCore);
		return *mConflictingCore;
	}
	
	bool hasAssignment(carl::Variable v) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Assignment for " << v);
		RootIndexer ri;
		std::map<ConstraintT, std::pair<std::vector<RAN>, ConstraintT>> rootMap;
		for (const auto& c: mConstraints) {
			if (!isUnivariate(c, v)) continue;
			ConstraintT cnew(carl::model::substitute(c.lhs(), mModel), c.relation());
			auto list = carl::model::realRoots(cnew.lhs(), v, mModel);
			ri.add(list);
			rootMap.emplace(c, std::make_pair(std::move(list), cnew));
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
				if (!satisfies(constraint, m, v, r)) {
					// Refutes root
					SMTRAT_LOG_TRACE("smtrat.nlsat", constraint << " refutes " << r << " -> " << 2*cur+1);
					setBitsForInterval(b, 2*cur+1, 2*cur+1);
				}
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
			mConflictingCore = std::vector<ConstraintT>();
			cover.buildConflictingCore(*mConflictingCore);
			return false;
		} else {
			mAssignment = ri.sampleFrom(cover.satisfyingInterval());
			return true;
		}
	}
};

}
