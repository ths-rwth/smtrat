#pragma once

#include <algorithm>
#include <iostream>
#include <vector>

#include "Bitset.h"

namespace smtrat {
namespace cad {

/**
 * This class represents one or more origins of some object.
 * An origin is a single id or a pair of ids (where a single id is represented as a pair of the same id).
 *
 * As an object can have multiple origins, this class stores a list of such pairs.
 * This class makes sure that the pairs are unique.
 */
class Origin {
public:
	struct BaseType: public std::pair<std::size_t,std::size_t> {
		using Super = std::pair<std::size_t,std::size_t>;
		explicit BaseType(std::size_t id): Super(id,id) {}
		BaseType(std::size_t id1, std::size_t id2): Super(id1,id2) {
			if (id1 > id2) std::swap(first, second);
		}
	};
private:
	std::vector<BaseType> mData;
	
	void makeUnique() {
		std::sort(mData.begin(), mData.end());
		mData.erase(std::unique(mData.begin(), mData.end()), mData.end());
	}
	template<typename F>
	void removeFiltered(F&& f) {
		auto it = std::remove_if(mData.begin(), mData.end(), f);
		mData.erase(it, mData.end());
	}
public:
	Origin() {}
	Origin(const Origin& po): mData(po.mData) {}
	Origin(Origin&& po): mData(std::move(po.mData)) {}
	
	explicit Origin(std::size_t id): mData(1, BaseType(id)) {}
	explicit Origin(const BaseType& bt): mData(1, bt) {}
	
	Origin& operator=(const Origin& rhs) {
		mData = rhs.mData;
		return *this;
	}
	Origin& operator=(Origin&& rhs) {
		mData = std::move(rhs.mData);
		return *this;
	}
	
	bool empty() const {
		return mData.empty();
	}
	
	bool operator==(const Origin& rhs) const {
		return mData == rhs.mData;
	}
	/// Adds the pair to the origins.
	Origin& operator+=(const BaseType& rhs) {
		mData.emplace_back(rhs);
		makeUnique();
		return *this;
	}
	/// Removes the pair from the origins.
	Origin& operator-=(const BaseType& rhs) {
		removeFiltered([&](const BaseType& bt){ return bt == rhs; });
		return *this;
	}
	// Removes all pairs that contain rhs.
	Origin& operator-=(std::size_t rhs) {
		removeFiltered([&](const BaseType& bt){ return bt.first == rhs || bt.second == rhs; });
		return *this;
	}
	// Removes all pairs that contain any bit from rhs.
	Origin& operator-=(const Bitset& rhs) {
		removeFiltered([&](const BaseType& bt){ return rhs.test(bt.first) || rhs.test(bt.second); });
		return *this;
	}
	
	Origin operator|(const Origin& rhs) const {
		Origin res(rhs);
		res.mData.insert(res.mData.end(), mData.begin(), mData.end());
		res.makeUnique();
		return res;
	}

	friend std::ostream& operator<<(std::ostream& os, const Origin& po) {
		return os << po.mData;
	}
};

}
}
