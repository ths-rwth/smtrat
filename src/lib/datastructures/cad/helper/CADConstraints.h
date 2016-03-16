#pragma once

#include <map>
#include <vector>

#include "../Common.h"

namespace smtrat {
namespace cad {

class BaseCADConstraints {
public:
	using Callback = std::function<void(const UPoly&, std::size_t)>;
protected:
	Variables mVariables;
	Callback mAddCallback;
	Callback mRemoveCallback;
	void callCallback(const Callback& cb, const ConstraintT& c, std::size_t id) const {
		cb(c.lhs().toUnivariatePolynomial(mVariables.front()), id);
	}
public:
	BaseCADConstraints(const Callback& onAdd, const Callback& onRemove): mAddCallback(onAdd), mRemoveCallback(onRemove) {}
	void reset(const Variables& vars) {
		mVariables = vars;
	}
};

template<Backtracking BT>
class CADConstraints {};

template<>
class CADConstraints<Backtracking::ORDERED>: public BaseCADConstraints {
private:
	using Super = BaseCADConstraints;
	using Super::Callback;
	std::vector<ConstraintT> mConstraints;
public:
	CADConstraints(const Callback& onAdd, const Callback& onRemove): Super(onAdd, onRemove) {}
	void reset(const Variables& vars) {
		Super::reset(vars);
		mConstraints.clear();
	}
	auto get() const {
		return mConstraints;
	}
	auto begin() const {
		return mConstraints.begin();
	}
	auto end() const {
		return mConstraints.end();
	}
	void add(const ConstraintT& c) {
		assert(!mVariables.empty());
		mConstraints.push_back(c);
		callCallback(mAddCallback, c, mConstraints.size()-1);
	}
	void remove(const ConstraintT& c) {
		std::stack<ConstraintT> cache;
		// Remove constraints added after c
		while (!mConstraints.empty() && mConstraints.back() != c) {
			callCallback(mRemoveCallback, mConstraints.back(), mConstraints.size()-1);
			cache.push(mConstraints.back());
			mConstraints.pop_back();
		}
		assert(mConstraints.back() == c);
		// Remove c
		callCallback(mRemoveCallback, mConstraints.back(), mConstraints.size()-1);
		mConstraints.pop_back();
		// Add constraints removed before
		while (!cache.empty()) {
			callCallback(mAddCallback, cache.top(), mConstraints.size());
			mConstraints.push_back(cache.top());
			cache.pop();
		}
	}
};

template<>
class CADConstraints<Backtracking::UNORDERED>: public BaseCADConstraints {
private:
	using Super = BaseCADConstraints;
	using Super::Callback;
	std::map<ConstraintT, std::size_t> mConstraints;
	IDPool mIDPool;
public:
	CADConstraints(const Callback& onAdd, const Callback& onRemove): Super(onAdd, onRemove) {}
	void reset(const Variables& vars) {
		Super::reset(vars);
		mConstraints.clear();
	}
	auto get() const {
		return mConstraints;
	}
	auto begin() const {
		return mConstraints.begin();
	}
	auto end() const {
		return mConstraints.end();
	}
	void add(const ConstraintT& c) {
		assert(!mVariables.empty());
		std::size_t id = mIDPool.get();
		auto res = mConstraints.emplace(c, id);
		assert(res.second);
		callCallback(mAddCallback, c, id);
	}
	void remove(const ConstraintT& c) {
		auto it = mConstraints.find(c);
		assert(it != mConstraints.end());
		std::size_t id = it->second;
		callCallback(mRemoveCallback, c, id);
		mConstraints.erase(it);
		mIDPool.free(id);
	}
};
	
}
}
