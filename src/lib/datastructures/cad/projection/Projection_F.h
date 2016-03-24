#pragma once

#include <iostream>
#include <map>
#include <vector>

#include "../Common.h"
#include "BaseProjection.h"

namespace smtrat {
namespace cad {
	
	template<typename Settings, Backtracking BT>
	class Projection<Incrementality::FULL, BT, Settings>: public BaseProjection {
	private:
		// A projection candidate of ids that refer to the parent level.
		using QueueEntry = std::pair<std::size_t,std::size_t>;
		struct ProjectionCandidateComparator {
		public:
			using PolyGetter = std::function<const UPoly&(std::size_t)>;
			ProjectionCandidateComparator(const PolyGetter& pg): mPG(pg) {}
			bool operator()(const QueueEntry& lhs, const QueueEntry& rhs) const {
				assert(mPG);
				const UPoly& lp = mPG(lhs.first);
				const UPoly& lq = mPG(lhs.second);
				const UPoly& rp = mPG(rhs.first);
				const UPoly& rq = mPG(rhs.second);
				return rp < lp;
			}
		private:
			PolyGetter mPG;
		};
		
		// Original polynomials indexed by their constraint ID.
		std::vector<boost::optional<UPoly>> mOriginalPolynomials;
		// Maps polynomials to a (per level) unique ID.
		std::vector<std::map<UPoly,std::size_t>> mPolynomialIDs;
		// Stores polynomials with their origins, being pairs of polynomials from the level above.
		std::vector<std::vector<boost::optional<std::pair<UPoly,Origin>>>> mPolynomials;
		// Stores the projection queues for each level.
		std::vector<PriorityQueue<QueueEntry,ProjectionCandidateComparator>> mProjectionQueues;
		
		
		const UPoly& getOriginalPolynomialById(std::size_t id) const {
			assert(id < mOriginalPolynomials.size());
			assert(mOriginalPolynomials[id]);
			return *mOriginalPolynomials[id];
		}
		
		void insertIntoProjectionQueue(std::size_t level, std::size_t id) {
			if (level >= dim()) return;
			mProjectionQueues[level].emplace(id, id);
			for (const auto& it: mPolynomialIDs[level]) {
				mProjectionQueues[level].emplace(it.second, id);
			}
		}
		void purgeFromProjectionQueue(std::size_t level, std::size_t id) {
			if (level >= dim()) return;
			mProjectionQueues[level].removeIf([&](const QueueEntry& qe){ return qe.first == id || qe.second == id; });
		}
		/// Inserts a polynomial with the given origin into the given level.
		void insertPolynomialTo(std::size_t level, const UPoly& p, const Origin::BaseType& origin) {
			auto it = mPolynomialIDs[level].find(p);
			if (it != mPolynomialIDs[level].end()) {
				assert(mPolynomials[level][it->second]);
				mPolynomials[level][it->second]->second += origin;
				return;
			}
			std::size_t id = getID(level);
			insertIntoProjectionQueue(level + 1, id);
			if (id >= mPolynomials.size()) mPolynomials[level].resize(id+1);
			assert(!mPolynomials[level][id]);
			mPolynomials[level][id] = std::make_pair(p, Origin(origin));
			mLiftingQueues[level].insert(id);
			mPolynomialIDs[level].emplace(p, id);
		}
		/// Removed the polynomial given by the iterator from all datastructures.
		template<typename Iterator>
		Iterator removePolynomialByIT(std::size_t level, Iterator it) {
			assert(it != mPolynomialIDs[level].end());
			std::size_t id = it->second;
			assert(mPolynomials[level][id]);
			purgeFromProjectionQueue(level + 1, id);
			mPolynomials[level][id] = boost::none;
			mLiftingQueues[level].erase(id);
			freeID(level, id);
			return mPolynomialIDs[level].erase(it);
		}
		
		bool projectIntoBase(const ConstraintSelection& cs) {
			auto& queue = mProjectionQueues[0];
			if (queue.empty()) return false;
			auto qe = queue.top();
			queue.pop();
			assert(qe.first == qe.second && mOriginalPolynomials[qe.first]);
			insertPolynomialTo(0, *mOriginalPolynomials[qe.first], Origin::BaseType(qe.first));
			return true;
		}
		bool projectInto(std::size_t level, const ConstraintSelection& cs) {
			if (level == 0) return projectIntoBase(cs);
			std::size_t oldSize = size(level);
			auto& queue = mProjectionQueues[level];
			while (true) {
				while (!queue.empty()) {
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Using next projection candidate " << queue.top() << " from " << queue);
					projectCandidate(level, queue.top());
					queue.pop();
					if (size(level) > oldSize) return true;
				}
				if (!projectInto(level-1, cs)) return false;
			}
			return false;
		}
		void projectCandidate(std::size_t level, const QueueEntry& qe) {
			if (qe.first == qe.second) {
				assert(mPolynomials[level-1][qe.first]);
				const auto& p = *mPolynomials[level-1][qe.first];
				mOperator(Settings::projectionOperator, p.first, var(level), 
					[&](const UPoly& np){ insertPolynomialTo(level, np, Origin::BaseType(qe.first)); }
				);
			} else {
				assert(mPolynomials[level-1][qe.first] && mPolynomials[level-1][qe.second]);
				const auto& p = *mPolynomials[level-1][qe.first];
				const auto& q = *mPolynomials[level-1][qe.second];
				mOperator(Settings::projectionOperator, p.first, q.first, var(level), 
					[&](const UPoly& np){ insertPolynomialTo(level, np, Origin::BaseType(qe.first,qe.second)); }
				);
			}
		}
		
	public:
		void reset(const std::vector<carl::Variable>& vars) {
			BaseProjection::reset(vars);
			mOriginalPolynomials.clear();
			mOriginalPolynomials.resize(dim());
			mPolynomialIDs.clear();
			mPolynomialIDs.resize(dim());
			mPolynomials.clear();
			mPolynomials.resize(dim());
			mProjectionQueues.clear();
			mProjectionQueues.emplace_back(ProjectionCandidateComparator([&](std::size_t id){ return getOriginalPolynomialById(id); }));
			for (std::size_t level = 1; level < dim(); level++) {
				mProjectionQueues.emplace_back(ProjectionCandidateComparator([&](std::size_t id){ return getPolynomialById(level-1,id); }));
			}
		}
		void addPolynomial(const UPoly& p, std::size_t cid) {
			if (cid >= mOriginalPolynomials.size()) {
				mOriginalPolynomials.resize(cid+1);
			}
			assert(!mOriginalPolynomials[cid]);
			mOriginalPolynomials[cid] = p;
			assert(mProjectionQueues.size() > 0);
			mProjectionQueues[0].emplace(cid,cid);
		}
		void removePolynomial(const UPoly& p, std::size_t cid) {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Removing " << cid);
			mOriginalPolynomials[cid] = boost::none;
			Bitset filter = Bitset().set(cid);
			for (std::size_t level = 0; level < dim(); level++) {
				Bitset removed;
				for (auto it = mPolynomialIDs[level].begin(); it != mPolynomialIDs[level].end();) {
					std::size_t id = it->second;
					assert(mPolynomials[level][id]);
					mPolynomials[level][id]->second -= filter;
					if (mPolynomials[level][id]->second.empty()) {
						removed.set(id);
						it = removePolynomialByIT(level, it);
					} else {
						it++;
					}
				}
				SMTRAT_LOG_TRACE("smtrat.cad.projection", "Calling callback for level " << level << ", removed [" << removed << "]");
				callRemoveCallback(level, removed);
				filter = removed;
			}
		}
		
		std::size_t size(std::size_t level) const {
			return mPolynomialIDs[level].size();
		}
		bool empty(std::size_t level) const {
			return mPolynomialIDs[level].empty();
		}
		
		bool projectNewPolynomial(std::size_t level, const ConstraintSelection& cs = Bitset(true)) {
			return projectInto(level, cs);
		}
		
		OptionalID getPolyForLifting(std::size_t level, SampleLiftedWith& slw) {
			return OptionalID();
		}
		OptionalID getPolyForLifting(std::size_t level, SampleLiftedWith& slw, const ConstraintSelection& cs) {
			return OptionalID();
		}
		
		const UPoly& getPolynomialById(std::size_t level, std::size_t id) const {
			assert(level < mPolynomials.size());
			assert(id < mPolynomials[level].size());
			assert(mPolynomials[level][id]);
			return mPolynomials[level][id]->first;
		}
		
		template<typename S, Backtracking B>
		friend std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::FULL, B, S>& p) {
			return os;
		}
	};
}
}
