#pragma once

#include <map>
#include <set>
#include <vector>

#include "../Common.h"

namespace smtrat {
namespace cad {

template<Backtracking BT>
class CADConstraints {
public:
	using Callback = std::function<void(const UPoly&, std::size_t)>;
	template<Backtracking B>
	friend std::ostream& operator<<(std::ostream& os, const CADConstraints<B>& cc);
protected:
	struct ConstraintComparator {
		std::size_t complexity(const ConstraintT& c) const {
			return c.maxDegree() * c.variables().size() * c.lhs().size();
		}
		bool operator()(const ConstraintT& lhs, const ConstraintT& rhs) const {
			auto cl = complexity(lhs);
			auto cr = complexity(rhs);
			if (cl != cr) return cl < cr;
			return lhs < rhs;
		}
	};
	using ConstraintMap = std::map<ConstraintT, std::size_t, ConstraintComparator>;
	using ConstraintIts = std::vector<typename ConstraintMap::iterator>;
	
	Variables mVariables;
	Callback mAddCallback;
	Callback mRemoveCallback;
	ConstraintMap mConstraintMap;
	std::vector<typename ConstraintMap::iterator> mConstraintIts;
	IDPool mIDPool;
	
	void callCallback(const Callback& cb, const ConstraintT& c, std::size_t id) const {
		if (cb) cb(c.lhs().toUnivariatePolynomial(mVariables.front()), id);
	}
public:
	CADConstraints(const Callback& onAdd, const Callback& onRemove): mAddCallback(onAdd), mRemoveCallback(onRemove) {}
	void reset(const Variables& vars) {
		mVariables = vars;
		mConstraintMap.clear();
		mConstraintIts.clear();
		mIDPool = IDPool();
	}
	std::size_t size() const {
		return mConstraintIts.size();
	}
	const auto& indexed() const {
		return mConstraintIts;
	}
	const auto& ordered() const {
		return mConstraintMap;
	}
	std::size_t add(const ConstraintT& c) {
		SMTRAT_LOG_DEBUG("smtrat.cad.constraints", "Adding " << c);
		assert(!mVariables.empty());
		std::size_t id = 0;
		if (BT == Backtracking::ORDERED) {
			id = mConstraintIts.size();
			mConstraintIts.push_back(mConstraintMap.end());
		} else {
			id = mIDPool.get();
			mConstraintIts.resize(id+1, mConstraintMap.end());
		}
		auto r = mConstraintMap.emplace(c, id);
		assert(r.second);
		mConstraintIts[id] = r.first;
		callCallback(mAddCallback, c, id);
		SMTRAT_LOG_DEBUG("smtrat.cad.constraints", "Result:" << std::endl << *this);
		return id;
	}
	std::size_t remove(const ConstraintT& c) {
		SMTRAT_LOG_DEBUG("smtrat.cad.constraints", "Removing " << c);
		auto it = mConstraintMap.find(c);
		assert(it != mConstraintMap.end());
		std::size_t id = it->second;
		assert(mConstraintIts[id] == it);
		if (BT == Backtracking::ORDERED) {
			SMTRAT_LOG_TRACE("smtrat.cad.constraints", "Removing " << id << " in ordered mode");
			std::stack<typename ConstraintMap::iterator> cache;
			// Remove constraints added after c
			while (mConstraintIts.back()->second > id) {
				SMTRAT_LOG_TRACE("smtrat.cad.constraints", "Preliminary removal of " << mConstraintIts.back()->first);
				callCallback(mRemoveCallback, mConstraintIts.back()->first, mConstraintIts.back()->second);
				cache.push(mConstraintIts.back());
				mConstraintIts.pop_back();
			}
			// Remove c
			SMTRAT_LOG_TRACE("smtrat.cad.constraints", "Actual removal of " << mConstraintIts.back()->first);
			callCallback(mRemoveCallback, mConstraintIts.back()->first, mConstraintIts.back()->second);
			mConstraintMap.erase(mConstraintIts.back());
			mConstraintIts.pop_back();
			if (mConstraintIts.size() != id) std::exit(45);
			assert(mConstraintIts.size() == id);
			// Add constraints removed before
			while (!cache.empty()) {
				SMTRAT_LOG_TRACE("smtrat.cad.constraints", "Readding of " << cache.top()->first);
				callCallback(mAddCallback, cache.top()->first, cache.top()->second);
				mConstraintIts.push_back(cache.top());
				cache.pop();
			}
		} else {
			callCallback(mRemoveCallback, c, id);
			mConstraintMap.erase(it);
			mConstraintIts[id] = mConstraintMap.end();
			mIDPool.free(id);
		}
		return id;
	}
	const ConstraintT& operator[](std::size_t id) const {
		assert(id < mConstraintIts.size());
		assert(mConstraintIts[id] != mConstraintMap.end());
		return mConstraintIts[id]->first;
	}
};

template<Backtracking BT>
std::ostream& operator<<(std::ostream& os, const CADConstraints<BT>& cc) {
	for (const auto& c: cc.mConstraintIts) {
		os << "\t" << c->second << ": " << c->first << std::endl;
	}
	return os;
}
	
}
}
