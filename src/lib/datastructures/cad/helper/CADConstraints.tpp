#include <algorithm>

namespace smtrat {
namespace cad {

template<Backtracking BT>
void CADConstraints<BT>::addToLevel(typename ConstraintMap::iterator it) {
	for (std::size_t i = 0; i < mVariables.size(); i++) {
		if (it->first.hasVariable(mVariables[i])) {
			mConstraintLevels[i].push_back(it);
			break;
		}
	}
}
template<Backtracking BT>
void CADConstraints<BT>::removeFromLevel(typename ConstraintMap::iterator it) {
	for (std::size_t i = 0; i < mVariables.size(); i++) {
		if (it->first.hasVariable(mVariables[i])) {
			auto clit = std::find(mConstraintLevels[i].begin(), mConstraintLevels[i].end(), it);
			assert(clit != mConstraintLevels[i].end());
			mConstraintLevels[i].erase(clit);
			break;
		}
	}
}
	
template<Backtracking BT>
void CADConstraints<BT>::reset(const Variables& vars) {
	mVariables = vars;
	mConstraintMap.clear();
	mConstraintIts.clear();
	mIDPool = IDPool();
	mConstraintLevels.clear();
	mConstraintLevels.resize(vars.size());
}

template<Backtracking BT>
std::size_t CADConstraints<BT>::add(const ConstraintT& c) {
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
	addToLevel(r.first);
	callCallback(mAddCallback, c, id);
	SMTRAT_LOG_DEBUG("smtrat.cad.constraints", "Result:" << std::endl << *this);
	return id;
}

template<Backtracking BT>
std::size_t CADConstraints<BT>::remove(const ConstraintT& c) {
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
		assert(mConstraintIts.back() == it);
		removeFromLevel(it);
		mConstraintMap.erase(it);
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
		removeFromLevel(it);
		mConstraintMap.erase(it);
		mConstraintIts[id] = mConstraintMap.end();
		mIDPool.free(id);
	}
	return id;
}

}
}
