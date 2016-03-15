#pragma once

#include <iostream>
#include <vector>

#include "Bitset.h"

namespace smtrat {
namespace cad {

/**
 * This class represents one or more origins of some object.
 * An origin is a set of other objects, represented by the set of their ids as a Bitset.
 *
 * As an object can have multiple origins, this class stores a list of such Bitsets.
 */
class Origin {
public:
	using BaseType = Bitset;
private:
	std::vector<BaseType> mData;
public:
	Origin() {}
	Origin(const Origin& po): mData(po.mData) {}
	Origin(Origin&& po): mData(std::move(po.mData)) {}
	
	explicit Origin(std::size_t id): mData(1, Bitset().set(id)) {}
	
	Origin& operator=(const Origin& rhs) {
		mData = rhs.mData;
		return *this;
	}
	Origin& operator=(Origin&& rhs) {
		mData = std::move(rhs.mData);
		return *this;
	}
	
	bool operator==(const Origin& rhs) const {
		return mData == rhs.mData;
	}
	
	Origin& operator-=(const BaseType& rhs) {
		for (auto it = mData.begin(); it != mData.end();) {
			if (*it == rhs) it = mData.erase(it);
			else it++;
		}
		return *this;
	}
	
	Origin operator|(const Origin& rhs) const {
		Origin res(rhs);
		res.mData.insert(res.mData.end(), mData.begin(), mData.end());
		std::sort(res.mData.begin(), res.mData.end());
		return res;
	}

	friend std::ostream& operator<<(std::ostream& os, const Origin& po) {
		return os << po.mData;
	}
};

}
}
