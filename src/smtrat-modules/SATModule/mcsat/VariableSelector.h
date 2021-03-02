#pragma once

#include "../../../Common.h"

#include <algorithm>
#include <map>
#include <vector>

namespace smtrat {
namespace mcsat {

class VariableSelector {
public:
	friend std::ostream& operator<<(std::ostream& os, const VariableSelector& vs);
private:
	using CounterMap = std::map<carl::Variable,std::pair<std::size_t,bool>>;
	/// Counts for every variable how often they occur in the constraints and whether they have already been decided
	CounterMap mCounter;
	/// A sorted list of variables still to consider
	mutable std::vector<carl::Variable> mQueue;
	/// A flag indicating whether mCounter has been changed
	mutable bool mCounterChanged = false;
	
	void fixQueue() const {
		if (mCounterChanged) {
			mQueue.clear();
			for (const auto& v: mCounter) {
				if (!v.second.second) {
					assert(v.second.first > 0);
					mQueue.push_back(v.first);
				}
			}
			auto order = [](carl::Variable a, carl::Variable b) { return a > b; };
			std::sort(mQueue.begin(), mQueue.end(), order);
			mCounterChanged = false;
		}
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Rebuilt queue: " << mQueue);
	}
	CounterMap::iterator find(carl::Variable v) {
		auto it = mCounter.find(v);
		assert(it != mCounter.end());
		assert(it->second.first > 0);
		return it;
	}
public:
	void add(const FormulaT& formula) {
		add(carl::arithmetic_variables(formula));
	}
	void add(const carl::carlVariables& vars) {
		for (auto v: vars) add(v);
	}
	void add(carl::Variable v) {
		auto it = mCounter.find(v);
		if (it == mCounter.end()) {
			it = mCounter.emplace(v, std::make_pair(0,false)).first;
			mCounterChanged = true;
		}
		it->second.first++;
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Added " << v << " -> " << mCounter);
	}
	void remove(const carl::Variables& vars) {
		for (auto v: vars) remove(v);
	}
	void remove(carl::Variable v) {
		auto it = find(v);
		it->second.first--;
		if (it->second.first == 0) {
			assert(!it->second.second);
			mCounter.erase(it);
			mCounterChanged = true;
		}
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Removed " << v << " -> " << mCounter);
	}
	
	void assign(carl::Variable v) {
		fixQueue();
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Assigned " << v << ", removing from queue " << *this);
		auto it = find(v);
		it->second.second = true;
		assert(mQueue.back() == v);
		mQueue.pop_back();
	}
	void unassign(carl::Variable v) {
		auto it = find(v);
		it->second.second = false;
		mCounterChanged = true;
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Unassigned " << v << ", added to queue " << *this);
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

inline std::ostream& operator<<(std::ostream& os, const VariableSelector& vs) {
	return os << vs.mQueue;
}

}
}
