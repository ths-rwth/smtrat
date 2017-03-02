#pragma once

#include "../../../Common.h"

#include <algorithm>
#include <map>
#include <vector>

namespace smtrat {
namespace mcsat {

class VariableSelector {
private:
	using CounterMap = std::map<carl::Variable,std::pair<std::size_t,bool>>;
	/// Counters for every variable how often they occur in the constraints and whether they have already been decided
	CounterMap mCounter;
	/// A sorted list of variables still to consider
	mutable std::vector<carl::Variable> mQueue;
	/// A flag indicating whether mCounter has been changed
	mutable bool mCounterChanged = false;
	
	void fixQueue() const {
		SMTRAT_LOG_TRACE("smtrat.sat.mc", "Rebuilding queue");
		if (mCounterChanged) {
			mQueue.clear();
			for (const auto& v: mCounter) {
				if (!v.second.second) {
					assert(v.second.first > 0);
					mQueue.push_back(v.first);
				}
			}
			auto order = [](carl::Variable a, carl::Variable b) { return a < b; };
			std::sort(mQueue.begin(), mQueue.end(), order);
			mCounterChanged = false;
		}
		SMTRAT_LOG_TRACE("smtrat.sat.mc", "-> " << mQueue);
	}
	CounterMap::iterator find(carl::Variable v) {
		auto it = mCounter.find(v);
		assert(it != mCounter.end());
		assert(it->second.first > 0);
		return it;
	}
public:
	void add(const carl::Variables& vars) {
		for (auto v: vars) add(v);
	}
	void add(carl::Variable v) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Adding " << v);
		auto it = mCounter.find(v);
		if (it == mCounter.end()) {
			it = mCounter.emplace(v, std::make_pair(0,false)).first;
			mCounterChanged = true;
		}
		it->second.first++;
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "-> " << mCounter);
	}
	void remove(const carl::Variables& vars) {
		for (auto v: vars) remove(v);
	}
	void remove(carl::Variable v) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Removing " << v);
		auto it = find(v);
		it->second.first--;
		if (it->second.first == 0) {
			assert(!it->second.second);
			mCounter.erase(it);
			mCounterChanged = true;
		}
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "-> " << mCounter);
	}
	
	void assign(carl::Variable v) {
		auto it = find(v);
		it->second.second = true;
		assert(mQueue.back() == v);
		mQueue.pop_back();
	}
	void unassign(carl::Variable v) {
		auto it = find(v);
		it->second.second = false;
		mCounterChanged = true;
	}
	
	bool empty() const {
		fixQueue();
		return mQueue.empty();
	}
	carl::Variable top() const {
		fixQueue();
		return mQueue.back();
	}
};

}
}
