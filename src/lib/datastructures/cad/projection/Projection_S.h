#pragma once

#include <iostream>
#include <map>
#include <vector>

#include "../Common.h"
#include "BaseProjection.h"
#include "Projection_NO.h"

namespace smtrat {
namespace cad {
	
	template<typename Settings, Backtracking BT>
	class Projection<Incrementality::SIMPLE, BT, Settings>: public Projection<Incrementality::NONE, Backtracking::UNORDERED, Settings> {
	private:
		template<typename S, Backtracking B>
		friend std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::SIMPLE, B, S>& p);
		using Super = Projection<Incrementality::NONE, Backtracking::UNORDERED, Settings>;
		struct QueueEntry {
			UPoly poly;
			std::size_t cid;
			bool isBound;
			QueueEntry(const UPoly& p, std::size_t c, bool b): poly(p), cid(c), isBound(b) {}
			bool operator==(const QueueEntry& qe) const {
				return (cid == qe.cid) && (poly == qe.poly);
			}
			friend std::ostream& operator<<(std::ostream& os, const QueueEntry& qe) {
				return os << "(" << qe.poly << "," << qe.cid << ")";
			}
		};
		
		struct PolynomialComparator {
			bool operator()(const QueueEntry& lhs, const QueueEntry& rhs) const {
				return lhs.poly.complexity() > rhs.poly.complexity();
			}
		};
		
		PriorityQueue<QueueEntry, PolynomialComparator> mQueue;
	public:
		template<typename ...Args>
		Projection(Args&&... args): Super(std::forward<Args>(args)...) {}
		void reset() {
			Super::reset();
			mQueue.clear();
		}
		carl::Bitset addPolynomial(const UPoly& p, std::size_t cid, bool isBound) {
			mQueue.push(QueueEntry(p, cid, isBound));
			return carl::Bitset();
		}
		void removePolynomial(const UPoly& p, std::size_t cid, bool isBound) {
			auto it = mQueue.find(QueueEntry(p, cid, false));
			if (it != mQueue.end()) {
				mQueue.erase(it);
			} else {
				Super::removePolynomial(p, cid, isBound);
			}
		}
		
		carl::Bitset projectNewPolynomial(const ConstraintSelection& = carl::Bitset(true)) {
			while (!mQueue.empty()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Using next polynomial " << mQueue.top() << " from " << mQueue);
				carl::Bitset res = Super::addPolynomial(mQueue.top().poly, mQueue.top().cid, mQueue.top().isBound);
				mQueue.pop();
				if (res.any()) return res;
			}
			return carl::Bitset();
		}	
	};
	
	template<typename S, Backtracking B>
	std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::SIMPLE, B, S>& p) {
		os << "Queue: " << p.mQueue << std::endl;
		return os << static_cast<const Projection<Incrementality::NONE, Backtracking::UNORDERED, S>&>(p);
	}
}
}
