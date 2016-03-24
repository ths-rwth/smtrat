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
			using PolyGetter = std::function<UPoly(std::size_t)>;
			ProjectionCandidateComparator(const PolyGetter& pg): mPG(pg) {}
			ProjectionCandidateComparator() = delete;
			ProjectionCandidateComparator(const ProjectionCandidateComparator& pcc): mPG(pcc.mPG) {}
			bool operator()(const QueueEntry& lhs, const QueueEntry& rhs) const {
				assert(mPG);
				UPoly lp = mPG(lhs.first);
				UPoly lq = mPG(lhs.second);
				UPoly rp = mPG(rhs.first);
				UPoly rq = mPG(rhs.second);
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
		
		
		UPoly getOriginalPolynomialById(std::size_t id) const {
			assert(id < mOriginalPolynomials.size());
			assert(mOriginalPolynomials[id]);
			return *(mOriginalPolynomials[id]);
		}
		
		void insertIntoProjectionQueue(std::size_t level, std::size_t id) {
			assert(level < dim());
			assert(level > 0);
			for (const auto& it: mPolynomialIDs[level-1]) {
				mProjectionQueues[level].emplace(it.second, id);
			}
		}
		void purgeFromProjectionQueue(std::size_t level, std::size_t id) {
			assert(level < dim());
			mProjectionQueues[level].removeIf([id](const QueueEntry& qe){ return qe.first == id || qe.second == id; });
		}
		/// Inserts a polynomial with the given origin into the given level.
		bool insertPolynomialTo(std::size_t level, const UPoly& p, const Origin::BaseType& origin) {
			if (canBePurged(p)) return false;
			if ((level > 0) && (level < dim() - 1) && canBeForwarded(level, p)) {
				return insertPolynomialTo(level+1, p.switchVariable(var(level+1)), origin);
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Inserting " << p << " into level " << level);
			assert(level < dim());
			auto it = mPolynomialIDs[level].find(p);
			if (it != mPolynomialIDs[level].end()) {
				assert(mPolynomials[level][it->second]);
				mPolynomials[level][it->second]->second += origin;
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Polynomial was already present, merged origins");
				return false;
			}
			std::size_t id = getID(level);
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Got new id " << id);
			if (id >= mPolynomials[level].size()) mPolynomials[level].resize(id+1);
			assert(!mPolynomials[level][id]);
			mPolynomials[level][id] = std::make_pair(p, Origin(origin));
			mLiftingQueues[level].insert(id);
			mPolynomialIDs[level].emplace(p, id);
			if (level < dim()-1) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Inserting into queue.");
				insertIntoProjectionQueue(level + 1, id);
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Done.");
			return true;
		}
		/// Removed the polynomial given by the iterator from all datastructures.
		template<typename Iterator>
		Iterator removePolynomialByIT(std::size_t level, Iterator it) {
			assert(it != mPolynomialIDs[level].end());
			std::size_t id = it->second;
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Removing " << id << " on " << level);
			assert(mPolynomials[level][id]);
			if (level < dim() - 1) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Purging from queue on level " << (level+1));
				purgeFromProjectionQueue(level + 1, id);
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Removing polynomial");
			mLiftingQueues[level].erase(id);
			mPolynomials[level][id] = boost::none;
			freeID(level, id);
			return mPolynomialIDs[level].erase(it);
		}
		
		bool projectIntoBase(const ConstraintSelection& cs) {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting into level 0");
			auto& queue = mProjectionQueues[0];
			if (queue.empty()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Nothing to project");
				return false;
			}
			auto qe = queue.top();
			queue.pop();
			assert(qe.first == qe.second && mOriginalPolynomials[qe.first]);
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> About to project " << qe.first);
			insertPolynomialTo(0, *mOriginalPolynomials[qe.first], Origin::BaseType(qe.first));
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Projected " << *mOriginalPolynomials[qe.first]);
			return true;
		}
		bool projectInto(std::size_t level, const ConstraintSelection& cs) {
			if (level == 0) return projectIntoBase(cs);
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting into level " << level);
			std::size_t oldSize = size(level);
			auto& queue = mProjectionQueues[level];
			while (true) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Current state at level " << level << ":" << std::endl << *this);
				while (!queue.empty()) {
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Using next projection candidate " << queue.top() << " from " << queue);
					bool worked = projectCandidateInto(level, queue.top());
					queue.pop();
					if (worked) return true;
				}
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Calling projection into above level " << (level-1));
				if (!projectInto(level-1, cs)) {
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> got nothing");
					// May have new polynomials anyway due to optimization in insertPolynomialTo()
					return size(level) > oldSize;
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> We should not get here");
			return false;
		}
		bool projectCandidateInto(std::size_t level, const QueueEntry& qe) {
			bool worked = false;
			if (qe.first == qe.second) {
				assert(qe.first < mPolynomials[level-1].size());
				assert(mPolynomials[level-1][qe.first]);
				const auto& p = *mPolynomials[level-1][qe.first];
				mOperator(Settings::projectionOperator, p.first, var(level), 
					[&](const UPoly& np){ worked = worked || insertPolynomialTo(level, np, Origin::BaseType(qe.first)); }
				);
			} else {
				assert(mPolynomials[level-1][qe.first] && mPolynomials[level-1][qe.second]);
				const auto& p = *mPolynomials[level-1][qe.first];
				const auto& q = *mPolynomials[level-1][qe.second];
				mOperator(Settings::projectionOperator, p.first, q.first, var(level), 
					[&](const UPoly& np){ worked = worked || insertPolynomialTo(level, np, Origin::BaseType(qe.first,qe.second)); }
				);
			}
			return worked;
		}
		
	public:
		void reset(const std::vector<carl::Variable>& vars) {
			BaseProjection::reset(vars);
			mOriginalPolynomials.clear();
			mPolynomialIDs.clear();
			mPolynomialIDs.resize(dim());
			mPolynomials.clear();
			mPolynomials.resize(dim());
			mProjectionQueues.clear();
			mProjectionQueues.emplace_back(ProjectionCandidateComparator([&](std::size_t id){ return getOriginalPolynomialById(id); }));
			for (std::size_t level = 0; level < dim() - 1; level++) {
				mProjectionQueues.emplace_back(ProjectionCandidateComparator([level,this](std::size_t id){ return getPolynomialById(level,id); }));
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
			Bitset filter = Bitset().set(cid);
			for (std::size_t level = 0; level < dim(); level++) {
				Bitset removed;
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Purging from level " << level);
				for (auto it = mPolynomialIDs[level].begin(); it != mPolynomialIDs[level].end();) {
					std::size_t id = it->second;
					assert(mPolynomials[level][id]);
					mPolynomials[level][id]->second -= filter;
					if (mPolynomials[level][id]->second.empty()) {
						SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Purging " << id << " from level " << level);
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
			mOriginalPolynomials[cid] = boost::none;
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
		
		const UPoly& getPolynomialById(std::size_t level, std::size_t id) const {
			assert(level < mPolynomials.size());
			if (id >= mPolynomials[level].size()) std::exit(37);
			assert(id < mPolynomials[level].size());
			if (!mPolynomials[level][id]) std::exit(38);
			assert(mPolynomials[level][id]);
			return mPolynomials[level][id]->first;
		}
		
		template<typename S, Backtracking B>
		friend std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::FULL, B, S>& p) {
			os << "-1:\tP: " << p.mOriginalPolynomials << std::endl;
			for (std::size_t level = 0; level < p.dim(); level++) {
				os << level << ":\tP: " << p.mPolynomials[level] << std::endl;
				os << "\tQ: " << p.mProjectionQueues[level] << std::endl;
				os << "\tL: " << p.mLiftingQueues[level] << std::endl;
			}
			return os;
		}
	};
}
}
