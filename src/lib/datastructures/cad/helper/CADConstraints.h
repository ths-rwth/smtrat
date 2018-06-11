#pragma once

#include <algorithm>
#include <map>
#include <set>
#include <vector>

#include "../../VariableBounds.h"
#include "../Common.h"
#include "../debug/DotHelper.h"

namespace smtrat {
namespace cad {

template<Backtracking BT>
class CADConstraints {
public:
	using Callback = std::function<void(const UPoly&, std::size_t, bool)>;
	using VariableBounds = vb::VariableBounds<ConstraintT>;
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
        Callback mAddEqCallback; 
	Callback mRemoveCallback;
	ConstraintMap mActiveConstraintMap;
	ConstraintMap mConstraintMap;
	std::vector<typename ConstraintMap::iterator> mConstraintIts;
	std::vector<std::size_t> mConstraintLevels;
	carl::IDPool mIDPool;
	VariableBounds mBounds;
	/// List of constraints that are satisfied by bounds.
	carl::Bitset mSatByBounds;
	/// List of constraints that are infeasible due to bounds.
	carl::Bitset mUnsatByBounds;
	
	template<typename CB, typename... Args>
	void callCallback(const CB& cb, const ConstraintT& c, Args... args) const {
		if (cb) cb(c.lhs().toUnivariatePolynomial(mVariables.front()), std::forward<Args>(args)...);
	}
public:
	CADConstraints(const Callback& onAdd, const Callback& onAddEq, const Callback& onRemove): mAddCallback(onAdd), mAddEqCallback(onAddEq), mRemoveCallback(onRemove) {}
	CADConstraints(const CADConstraints&) = delete;
	void reset(const Variables& vars) {
		mVariables = vars;
		mActiveConstraintMap.clear();
		mConstraintMap.clear();
		mConstraintIts.clear();
		mIDPool.clear();
	}
	const Variables& vars() const {
		return mVariables;
	}
	std::size_t size() const {
		return mConstraintIts.size();
	}
	bool valid(std::size_t id) const {
		return mConstraintIts[id] != mConstraintMap.end();
	}
	const auto& indexed() const {
		return mConstraintIts;
	}
	const auto& ordered() const {
		return mActiveConstraintMap;
	}
	const auto& bounds() const {
		return mBounds;
	}
	const auto& unsatByBounds() const {
		return mUnsatByBounds;
	}
	std::size_t add(const ConstraintT& c) {
		SMTRAT_LOG_DEBUG("smtrat.cad.constraints", "Adding " << c << " to " << std::endl << *this);
		bool isBound = mBounds.addBound(c, c);
		assert(!mVariables.empty());
		std::size_t id = 0;
		if (BT == Backtracking::ORDERED) {
			id = mConstraintIts.size();
			mConstraintIts.push_back(mConstraintMap.end());
			mConstraintLevels.emplace_back(0);
                       
		       	mActiveConstraintMap.emplace(c, id);	
                        auto r = mConstraintMap.emplace(c, id);
                        assert(r.second);
                        mConstraintIts[id] = r.first;
                } else if (BT == Backtracking::HIDE) {
                        auto it = mConstraintMap.find(c);
			if (it != mConstraintMap.end()) {
				id = it->second;
				mActiveConstraintMap.emplace(c, id);
				mConstraintIts[id] = it;
			} else {
				id = mIDPool.get();
				if (id >= mConstraintIts.size()) {
					mConstraintIts.resize(id+1, mConstraintMap.end());
					mConstraintLevels.resize(id+1);
				}
				mActiveConstraintMap.emplace(c, id);
				auto r = mConstraintMap.emplace(c, id);
				assert(r.second);
				mConstraintIts[id] = r.first;
			}
		} else {
			id = mIDPool.get();
			if (id >= mConstraintIts.size()) {
				mConstraintIts.resize(id+1, mConstraintMap.end());
				mConstraintLevels.resize(id+1);
			}
			mActiveConstraintMap.emplace(c, id);
                        auto r = mConstraintMap.emplace(c, id);
                        assert(r.second);
                        mConstraintIts[id] = r.first;
		}
		auto vars = c.variables();
		for (std::size_t level = mVariables.size(); level > 0; level--) {
			vars.erase(mVariables[level - 1]);
			if (vars.empty()) {
				mConstraintLevels[id] = level;
				break;
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.constraints", "Identified " << c << " as level " << mConstraintLevels[id]);
                if(c.relation() == carl::Relation::EQ) {
                        callCallback(mAddEqCallback, c, id, isBound);
                } else {
                        callCallback(mAddCallback, c, id, isBound);
                }
		SMTRAT_LOG_DEBUG("smtrat.cad.constraints", "Added " << c << " to " << std::endl << *this);
		return id;
	}
	
	/**
	 * Removes a constraint.
	 * Returns the set of constraint ids that have (possibly) been reassigned and should be cleared from the sample evaluations.
	 */
	carl::Bitset remove(const ConstraintT& c) {
		SMTRAT_LOG_DEBUG("smtrat.cad.constraints", "Removing " << c << " from " << std::endl << *this);
		bool isBound = mBounds.removeBound(c, c);
		auto it = mConstraintMap.find(c);
		assert(it != mConstraintMap.end());
		std::size_t id = it->second;
		carl::Bitset res = {id};
		mSatByBounds.reset(id);
		mUnsatByBounds.reset(id);
		assert(mConstraintIts[id] == it);
		if (BT == Backtracking::ORDERED) {
			SMTRAT_LOG_TRACE("smtrat.cad.constraints", "Removing " << id << " in ordered mode");
			std::stack<ConstraintT> cache;
			// Remove constraints added after c
			while (mConstraintIts.back()->second > id) {
				SMTRAT_LOG_TRACE("smtrat.cad.constraints", "Preliminary removal of " << mConstraintIts.back()->first);
				cache.push(mConstraintIts.back()->first);
				res |= remove(mConstraintIts.back()->first);
			}
			// Remove c
			SMTRAT_LOG_TRACE("smtrat.cad.constraints", "Actual removal of " << mConstraintIts.back()->first);
			callCallback(mRemoveCallback, mConstraintIts.back()->first, mConstraintIts.back()->second, isBound);
			mActiveConstraintMap.erase(mConstraintIts.back()->first);
			mConstraintMap.erase(mConstraintIts.back());
			mConstraintIts.pop_back();
			assert(mConstraintIts.size() == id);
			// Add constraints removed before
			while (!cache.empty()) {
				SMTRAT_LOG_TRACE("smtrat.cad.constraints", "Readding of " << cache.top());
				add(cache.top());
				cache.pop();
			}
                } else if(BT == Backtracking::HIDE) {
                        SMTRAT_LOG_TRACE("smtrat.cad.constraints", "Removing " << id << " in unordered mode");
			callCallback(mRemoveCallback, c, id, isBound);
			mActiveConstraintMap.erase(it->first);
			mConstraintIts[id] = mConstraintMap.end();
		} else {
			SMTRAT_LOG_TRACE("smtrat.cad.constraints", "Removing " << id << " in unordered mode");
			callCallback(mRemoveCallback, c, id, isBound);
			mActiveConstraintMap.erase(it->first);
			mConstraintMap.erase(it);
			mConstraintIts[id] = mConstraintMap.end();
			mIDPool.free(id); 
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.constraints", "Removed " << c << " from " << std::endl << *this);
		return res;
	}
	const ConstraintT& operator[](std::size_t id) const {
		assert(id < mConstraintIts.size());
		assert(mConstraintIts[id] != mConstraintMap.end());
		return mConstraintIts[id]->first;
	}
	std::size_t level(std::size_t id) const {
		return mConstraintLevels[id];
	}
	bool checkForTrivialConflict(std::vector<FormulaSetT>& mis) const {
		if (bounds().isConflicting()) {
			SMTRAT_LOG_INFO("smtrat.cad", "Trivially unsat due to bounds" << std::endl << bounds());
			mis.emplace_back();
			for (const auto& c: bounds().getOriginsOfBounds()) {
				mis.back().emplace(c);
			}
			return true;
		}
		const auto& intervalmap = mBounds.getIntervalMap();
		for (const auto& c: mConstraintIts) {
			if (c == mConstraintMap.end()) continue;
			SMTRAT_LOG_TRACE("smtrat.cad", "Checking " << c->first << " against " << intervalmap);
			switch (c->first.consistentWith(intervalmap)) {
				case 0: {
					SMTRAT_LOG_INFO("smtrat.cad", "Single constraint conflicts with bounds: " << c->first << std::endl << bounds());
					mis.emplace_back();
					for (const auto& b: bounds().getOriginsOfBounds()) {
						mis.back().emplace(b);
					}
					mis.back().emplace(c->first);
					return true;
				}
				default: break;
			}
		}
		return false;
	}
	void exportAsDot(std::ostream& out) const {
		debug::DotSubgraph dsg("constraints");
		for (const auto& c: mActiveConstraintMap) {
			out << "\t\tc_" << c.second << " [label=\"" << c.first << "\"];" << std::endl;
			dsg.add("c_" + std::to_string(c.second));
		}
		out << "\t" << dsg << std::endl;
	}
};

template<Backtracking BT>
std::ostream& operator<<(std::ostream& os, const CADConstraints<BT>& cc) {
	for (const auto& c: cc.mConstraintIts) {
		if (c == cc.mConstraintMap.end()) continue;
		os << "\t" << c->second << ": " << c->first << std::endl;
	}
	assert(long(cc.mActiveConstraintMap.size()) == std::count_if(cc.mConstraintIts.begin(), cc.mConstraintIts.end(), [&cc](auto it){ return it != cc.mConstraintMap.end(); }));
	return os;
}
	
}
}
