#pragma once

#include "../Common.h"

#include <iostream>
#include <set>

namespace smtrat {
namespace cad {
	
	template<typename PolynomialGetter>
	struct PolynomialComparator {
	private:
		const PolynomialGetter* mPG;
		std::size_t mLevel;
	public:
		PolynomialComparator(const PolynomialGetter* pg, std::size_t level): mPG(pg), mLevel(level) {}
		bool operator()(std::size_t lhs, std::size_t rhs) const {
			const UPoly& l = mPG->getPolynomialById(mLevel, lhs);
			const UPoly& r = mPG->getPolynomialById(mLevel, rhs);
			return l < r;
		}
	};

	template<typename PolynomialGetter>
	class PolynomialLiftingQueue {
		template<typename PG>
		friend std::ostream& operator<<(std::ostream& os, const PolynomialLiftingQueue<PG>& plq);
	private:
		PolynomialComparator<PolynomialGetter> mComparator;
		std::set<std::size_t, PolynomialComparator<PolynomialGetter>> mQueue;
		carl::Bitset mDisabled;
	public:
		PolynomialLiftingQueue(const PolynomialGetter* pg, std::size_t level):
			mComparator(pg, level),
			mQueue(mComparator)
		{}
		
		auto insert(std::size_t id) {
			return mQueue.insert(id);
		}
		auto erase(std::size_t id) {
			return mQueue.erase(id);
		}
		
		auto begin() const {
			return mQueue.begin();
		}
		auto end() const {
			return mQueue.end();
		}
		auto size() const {
			return mQueue.size();
		}

		void disable(std::size_t id) {
			erase(id);
			mDisabled.set(id, true);
		}
		void restore(std::size_t id) {
			if (mDisabled.test(id)) {
				mDisabled.set(id, false);
				insert(id);
			}
		}
		
	};
	template<typename PG>
	inline std::ostream& operator<<(std::ostream& os, const PolynomialLiftingQueue<PG>& plq) {
		return os << plq.mQueue;
	}

}
}
