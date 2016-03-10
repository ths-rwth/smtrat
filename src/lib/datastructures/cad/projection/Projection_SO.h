#pragma once

#include <iostream>
#include <map>
#include <vector>

#include "../Common.h"
#include "../utils/DynamicPriorityQueue.h"
#include "BaseProjection.h"
#include "Projection_NO.h"

namespace smtrat {
namespace cad {
	
	template<typename Settings>
	class Projection<Incrementality::SIMPLE, Backtracking::ORDERED, Settings>: public Projection<Incrementality::NONE, Backtracking::ORDERED, Settings> {
	private:
		using Super = Projection<Incrementality::NONE, Backtracking::ORDERED, Settings>;
		
		struct PolynomialComparator {
			bool operator()(const UPoly& lhs, const UPoly& rhs) const {
				return lhs < rhs;
			}
		};
		
		PriorityQueue<UPoly, PolynomialComparator> mQueue;
	public:
		void reset(const std::vector<carl::Variable>& vars) {
			Super::reset(vars);
			mQueue.clear();
		}
		void addPolynomial(const UPoly& p) {
			mQueue.push(p);
		}
		void removePolynomial(const UPoly& p, const std::function<void(std::size_t,SampleLiftedWith)>& callback) {
			auto it = mQueue.find(p);
			if (it != mQueue.end()) {
				mQueue.erase(it);
			} else {
				Super::removePolynomial(p, callback);
			}
		}
		
		bool projectNewPolynomial(std::size_t level, const ConstraintSelection& ps = Bitset(true)) {
			std::size_t oldSize = Super::size(level);
			while (!mQueue.empty()) {
				Super::addPolynomial(mQueue.top());
				mQueue.pop();
				if (Super::size(level) != oldSize) return true;
			}
			return false;
		}
		
		template<typename S>
		friend std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::SIMPLE, Backtracking::ORDERED, S>& p) {
			os << "Queue: " << p.mQueue << std::endl;
			return os << Projection<Incrementality::NONE, Backtracking::ORDERED, S>(p);
		}
	};
}
}
