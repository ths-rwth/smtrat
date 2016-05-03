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
		template<typename S, Backtracking B>
		friend std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::FULL, B, S>& p);
		// A projection candidate: a level to project into and two ids that refer to the level above.
		struct QueueEntry {
			std::size_t level;
			std::size_t first;
			std::size_t second;
			QueueEntry(std::size_t l, std::size_t f, std::size_t s): level(l), first(f), second(s) {}
			friend std::ostream& operator<<(std::ostream& os, const QueueEntry& qe) {
				return os << "(" << qe.first << "," << qe.second << ")@" << qe.level;
			}
		};
		struct ProjectionCandidateComparator {
		public:
			using PolyGetter = std::function<UPoly(std::size_t, std::size_t)>;
			ProjectionCandidateComparator(const PolyGetter& pg): mPG(pg) {}
			ProjectionCandidateComparator() = delete;
			ProjectionCandidateComparator(const ProjectionCandidateComparator& pcc): mPG(pcc.mPG) {}
			bool operator()(const QueueEntry& lhs, const QueueEntry& rhs) const {
				assert(mPG);
				UPoly lp = mPG(lhs.level, lhs.first);
				UPoly lq = mPG(lhs.level, lhs.second);
				UPoly rp = mPG(rhs.level, rhs.first);
				UPoly rq = mPG(rhs.level, rhs.second);
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
		// Stores the projection queue for all candidates
		PriorityQueue<QueueEntry,ProjectionCandidateComparator> mProjectionQueue;
		
		std::string logPrefix(std::size_t level) const {
			return std::string(dim() - level, '\t');
		}
		
		UPoly getOriginalPolynomialById(std::size_t id) const {
			assert(id < mOriginalPolynomials.size());
			assert(mOriginalPolynomials[id]);
			return *(mOriginalPolynomials[id]);
		}
		
		void insertIntoProjectionQueue(std::size_t level, std::size_t id) {
			assert(level < dim());
			assert(level > 0);
			for (const auto& it: mPolynomialIDs[level-1]) {
				mProjectionQueue.emplace(level, it.second, id);
			}
		}
		void purgeFromProjectionQueue(std::size_t level, std::size_t id) {
			assert(level < dim());
			mProjectionQueue.removeIf([level,id](const QueueEntry& qe){ return (qe.level == level) && (qe.first == id || qe.second == id); });
		}
		/// Inserts a polynomial with the given origin into the given level.
		Bitset insertPolynomialTo(std::size_t level, const UPoly& p, const Origin::BaseType& origin) {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "Receiving " << p << " for level " << level);
			if (canBePurged(p)) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> but is purged.");
				return Bitset();
			}
			if ((level > 0) && (level < dim() - 1) && canBeForwarded(level, p)) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> but is forwarded to " << (level+1));
				return insertPolynomialTo(level+1, p.switchVariable(var(level+1)), origin);
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "Inserting " << p << " into level " << level);
			assert(level < dim());
			auto it = mPolynomialIDs[level].find(p);
			if (it != mPolynomialIDs[level].end()) {
				assert(mPolynomials[level][it->second]);
				mPolynomials[level][it->second]->second += origin;
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Polynomial was already present, merged origins");
				return Bitset();
			}
			std::size_t id = getID(level);
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Got new id " << id);
			if (id >= mPolynomials[level].size()) mPolynomials[level].resize(id+1);
			assert(!mPolynomials[level][id]);
			mPolynomials[level][id] = std::make_pair(p, Origin(origin));
			mLiftingQueues[level].insert(id);
			mPolynomialIDs[level].emplace(p, id);
			if (level < dim()-1) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Inserting " << id << " into queue for level " << (level+1));
				insertIntoProjectionQueue(level + 1, id);
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Done.");
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Now:" << std::endl << *this);
			return Bitset({level});
		}
		/// Removed the polynomial given by the iterator from all datastructures.
		template<typename Iterator>
		Iterator removePolynomialByIT(std::size_t level, Iterator it) {
			assert(it != mPolynomialIDs[level].end());
			std::size_t id = it->second;
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "Removing " << id << " on " << level);
			assert(mPolynomials[level][id]);
			if (level < dim() - 1) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Purging from queue on level " << (level+1));
				purgeFromProjectionQueue(level + 1, id);
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Removing polynomial");
			mLiftingQueues[level].erase(id);
			mPolynomials[level][id] = boost::none;
			freeID(level, id);
			return mPolynomialIDs[level].erase(it);
		}
		
		Bitset project(const ConstraintSelection& cs) {
			while (!mProjectionQueue.empty()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting" << std::endl << *this);
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Using next projection candidate " << mProjectionQueue.top());
				QueueEntry qe = mProjectionQueue.top();
				mProjectionQueue.pop();
				Bitset res = projectCandidate(qe);
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> res = " << res);
				if (res.any()) return res;
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Projection is finished.");
			return Bitset();
		}
		Bitset projectBaseCandidate(const QueueEntry& qe) {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting into level 0");
			assert(qe.level == 0);
			assert(qe.first == qe.second && mOriginalPolynomials[qe.first]);
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> About to project " << qe.first);
			insertPolynomialTo(0, *mOriginalPolynomials[qe.first], Origin::BaseType(qe.first));
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Projected " << *mOriginalPolynomials[qe.first]);
			return Bitset({0});
		}
		Bitset projectCandidate(const QueueEntry& qe) {
			if (qe.level == 0) return projectBaseCandidate(qe);
			Bitset res;
			if (qe.first == qe.second) {
				assert(qe.first < mPolynomials[qe.level-1].size());
				assert(mPolynomials[qe.level-1][qe.first]);
				const auto& p = *mPolynomials[qe.level-1][qe.first];
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting single " << p << " into " << qe.level);
				mOperator(Settings::projectionOperator, p.first, var(qe.level), 
					[&](const UPoly& np){ res |= insertPolynomialTo(qe.level, np, Origin::BaseType(qe.first)); }
				);
			} else {
				assert(qe.first < mPolynomials[qe.level-1].size());
				assert(qe.second < mPolynomials[qe.level-1].size());
				assert(mPolynomials[qe.level-1][qe.first] && mPolynomials[qe.level-1][qe.second]);
				const auto& p = *mPolynomials[qe.level-1][qe.first];
				const auto& q = *mPolynomials[qe.level-1][qe.second];
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting paired " << p << ", " << q << " into " << qe.level);
				mOperator(Settings::projectionOperator, p.first, q.first, var(qe.level), 
					[&](const UPoly& np){ res |= insertPolynomialTo(qe.level, np, Origin::BaseType(qe.first,qe.second)); }
				);
			}
			return res;
		}
		
	public:
		Projection(): mProjectionQueue(ProjectionCandidateComparator([&](std::size_t level, std::size_t id){ return (level == 0) ? getOriginalPolynomialById(id) : getPolynomialById(level-1, id); })) {}
		void reset(const std::vector<carl::Variable>& vars) {
			BaseProjection::reset(vars);
			mOriginalPolynomials.clear();
			mPolynomialIDs.clear();
			mPolynomialIDs.resize(dim());
			mPolynomials.clear();
			mPolynomials.resize(dim());
			mProjectionQueue.clear();
		}
		Bitset addPolynomial(const UPoly& p, std::size_t cid) {
			if (cid >= mOriginalPolynomials.size()) {
				mOriginalPolynomials.resize(cid+1);
			}
			assert(!mOriginalPolynomials[cid]);
			mOriginalPolynomials[cid] = p;
			mProjectionQueue.emplace(0, cid, cid);
			return Bitset();
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
		
		Bitset projectNewPolynomial(const ConstraintSelection& cs = Bitset(true)) {
			return project(cs);
		}
		
		const UPoly& getPolynomialById(std::size_t level, std::size_t id) const {
			assert(level < mPolynomials.size());
			assert(id < mPolynomials[level].size());
			assert(mPolynomials[level][id]);
			return mPolynomials[level][id]->first;
		}
	};
	
	template<typename S, Backtracking B>
	std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::FULL, B, S>& p) {
		os << "-1:\tP: " << p.mOriginalPolynomials << std::endl;
		for (std::size_t level = 0; level < p.dim(); level++) {
			os << level << ":\tP: " << p.mPolynomials[level] << std::endl;
			os << "\tL: " << p.mLiftingQueues[level] << std::endl;
		}
		os << "Q: " << p.mProjectionQueue << std::endl;
		return os;
	}
}
}
