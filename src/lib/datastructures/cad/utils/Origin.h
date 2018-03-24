#pragma once

#include <carl/io/streamingOperators.h>
#include <carl/util/Bitset.h>

#include <algorithm>
#include <iostream>
#include <vector>

namespace smtrat {
namespace cad {
using carl::operator<<;

/**
 * This class represents one or more origins of some object.
 * An origin is a single id or a pair of ids (where a single id is represented as a pair of the same id).
 *
 * As an object can have multiple origins, this class stores a list of such pairs.
 * This class makes sure that the pairs are unique.
 */
class Origin {
public:
	struct BaseType {
		std::size_t level;
		std::size_t first;
		std::size_t second;
                bool f_act = true;
                bool s_act = true;
                bool e_act = true;
		explicit BaseType(std::size_t level, std::size_t id): BaseType(level,id,id) {}
		BaseType(std::size_t lvl, std::size_t id1, std::size_t id2): level(lvl),first(id1),second(id2) {
			if (first > second) std::swap(first, second);
		}
		bool operator==(const BaseType& bt) const {
			return (level == bt.level) && (first == bt.first) && (second == bt.second);
		}
		bool operator<(const BaseType& bt) const {
			if (level != bt.level) return level < bt.level;
			if (first != bt.first) return first < bt.first;
			return second < bt.second;
		}
		friend std::ostream& operator<<(std::ostream& os, const BaseType& bt) {
			return os << "(" << bt.first << "," << bt.second << ")@" << bt.level;
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
	
	explicit Origin(std::size_t level, std::size_t id): mData(1, BaseType(level, id)) {}
	explicit Origin(const BaseType& bt): mData(1, bt) {}
	
	auto begin() const {
		return mData.begin();
	}
	auto end() const {
		return mData.end();
	}
        
        // returns true, if Origin contains at least one active BaseType
        bool isActive() const {
                for(const auto& it : mData) {
                        if(it.f_act && it.s_act && it.e_act) {
                            return true;
                        }
                }
                return false;
        }
        
        // deactivates BaseTypes due to inactive polynomials 
        void deactivate(std::size_t level, const carl::Bitset& rhs) {
                for(auto& it : mData) {
                        if(it.level == level) {
                                if(rhs.test(it.first)) {
                                        it.f_act = false;
                                } else if(rhs.test(it.second)) {
                                        it.s_act = false;
                                }
                        }
                }
        }
        
        // deactivates BaseTypes due to equational constraint 
        void deactivateEC(std::size_t level, const carl::Bitset& rhs) {
                for(auto& it : mData) {
                        if((it.level == level) && !rhs.test(it.first) && !rhs.test(it.second)) {
                                it.e_act = false;
                        }
                }
        }
        
        // activates BaseTypes due to activated polynomials 
        void activate(std::size_t level, const carl::Bitset& rhs) {
                for(auto& it : mData) {
                        if(it.level == level) {
                                if(rhs.test(it.first)) {
                                        it.f_act = true;
                                } else if(rhs.test(it.second)) {
                                        it.s_act = true;
                                }
                        }
                }
        }
        
        // activates BaseTypes due to equational constraint that is not used for restricted projection anymore 
        void activateEC(std::size_t level, const carl::Bitset& rhs) {
                for(auto& it : mData) {
                        if((it.level == level) && !rhs.test(it.first) && !rhs.test(it.second)) {
                                it.e_act = true;
                        }
                }
        }
	
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
	Origin& erase(std::size_t level, const carl::Bitset& rhs) {
		removeFiltered([&](const BaseType& bt){ return (bt.level == level) && (rhs.test(bt.first) || rhs.test(bt.second)); });
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
