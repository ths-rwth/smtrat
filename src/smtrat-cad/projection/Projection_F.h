#pragma once

#include <iostream>
#include <map>
#include <vector>

#include "../common.h"
#include "../debug/DotHelper.h"
#include "BaseProjection.h"
#include "ProjectionComparator.h"

namespace smtrat {
namespace cad {
namespace full {
	using Polynomial = boost::optional<std::pair<UPoly,Origin>>;
}
	inline std::ostream& operator<<(std::ostream& os, const full::Polynomial& p) {
		if (!p) return os << "--";
		return os << p->first << " " << p->second;
	}
	
	template<typename Settings, Backtracking BT>
	class Projection<Incrementality::FULL, BT, Settings>: public BaseProjection<Settings> {
	private:
		using Super = BaseProjection<Settings>;
		using typename Super::Constraints;
		using Super::mConstraints;
		using Super::mLiftingQueues;
		using Super::mOperator;
		using Super::callRemoveCallback;
		using Super::canBePurgedByBounds;
		using Super::getID;
		using Super::freeID;
		using Super::var;
	public:
		using Super::dim;
		using Super::size;
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
				return mComparator(cad::candidate(lp, lq, lhs.level), cad::candidate(rp, rq, rhs.level));
				//return rp < lp;
			}
		private:
			PolyGetter mPG;
			ProjectionComparator<Settings::projectionComparator> mComparator;
		};

		struct PurgedPolynomials {
		private:
			struct PurgedLevel {
				mutable carl::Bitset evaluated;
				mutable carl::Bitset purged;
				carl::Bitset bounds;
				std::vector<QueueEntry> entries;
			};
			std::vector<PurgedLevel> mData;
			std::function<bool(std::size_t,std::size_t)> mCanBePurged;
			
			auto& data(std::size_t level) {
				assert(level >= 0 && level < mData.size());
				return mData[level];
			}
			const auto& data(std::size_t level) const {
				assert(level >= 0 && level < mData.size());
				return mData[level];
			}
		public:
			template<typename PurgeCheck>
			explicit PurgedPolynomials(const PurgeCheck& pc): mCanBePurged(pc) {}
			void reset(std::size_t dim) {
				mData.clear();
				mData.resize(dim);
			}
			void add(const QueueEntry& qe) {
				assert(qe.level < mData.size());
				data(qe.level).entries.push_back(qe);
			}
			void remove(std::size_t level, std::size_t id) {
				assert(level >= 0 && level < mData.size());
				data(level).evaluated.reset(id);
				data(level).purged.reset(id);
				auto it = std::remove_if(data(level).entries.begin(), data(level).entries.end(), [level,id](const QueueEntry& qe){
					return (qe.level == level) && (qe.first == id || qe.second == id);
				});
				data(level).entries.erase(it, data(level).entries.end());
			}
			void setBound(std::size_t level, std::size_t id, bool isBound) {
				assert(level > 0 && level <= mData.size());
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Setting " << level << "/" << id << " is a bound to " << isBound);
				data(level).bounds.set(id, isBound);
			}
			bool isPurged(std::size_t level, std::size_t id) const {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Checking whether " << level << "/" << id << " is purged.");
				assert(level >= 0 && level < mData.size());
				if (data(level).bounds.test(id)) {
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Do not purge as " << level << "/" << id << " is a bound.");
					return false;
				}
				if (!data(level).evaluated.test(id)) {
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Checking if " << level << "/" << id << " can be purged.");
					data(level).purged.set(id, mCanBePurged(level, id));
					data(level).evaluated.set(id);
				}
				return data(level).purged.test(id);
			}
			bool isPurged(const QueueEntry& qe) const {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Is " << qe << " purged?");
				assert(qe.level >= 0 && qe.level < mData.size());
				if (qe.level == 0) {
					assert(qe.first == qe.second);
					return mCanBePurged(0, qe.first);
				}
				return isPurged(qe.level, qe.first) || isPurged(qe.level, qe.second);
			}
			template<typename Restorer>
			void restore(const Restorer& r) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Resetting evaluation data and restoring entries.");
				for (auto& lvl: mData) {
					lvl.evaluated = carl::Bitset();
					lvl.purged = carl::Bitset();
				}
				for (auto& lvl: mData) {
					auto it = std::remove_if(lvl.entries.begin(), lvl.entries.end(),
					[this,&r](const QueueEntry& qe){
						if (isPurged(qe)) return false;
						r(qe);
						return true;
					});
					lvl.entries.erase(it, lvl.entries.end());
				}
			}
		};

		// Maps polynomials to a (per level) unique ID.
		std::vector<std::map<UPoly,std::size_t>> mPolynomialIDs;
		// Stores polynomials with their origins, being pairs of polynomials from the level above.
		std::vector<std::vector<full::Polynomial>> mPolynomials;
		// Stores the projection queue for all candidates
		PriorityQueue<QueueEntry,ProjectionCandidateComparator> mProjectionQueue;
		
		PurgedPolynomials mPurgedPolys;
		
		std::string logPrefix(std::size_t level) const {
			return std::string(dim() - level, '\t');
		}
		
		/**
		 * Add projection candidates for a new polynomial.
		 * @param level Level of the projection candidate
		 * @param id Id of the new polynomial
		 */
		void insertIntoProjectionQueue(std::size_t level, std::size_t id) {
			assert(level < dim());
			for (const auto& it: mPolynomialIDs[level]) {
				mProjectionQueue.emplace(level, it.second, id);
			}
		}
		/**
		 * Remove projection candidates involving a specific polynomial.
		 * @param level Level of the removed polynomial.
		 * @parem id Id of the removed polynomial.
		 */
		void removeFromProjectionQueue(std::size_t level, std::size_t id) {
			assert(level < dim());
			mProjectionQueue.removeIf([level,id](const QueueEntry& qe){ return (qe.level == level) && (qe.first == id || qe.second == id); });
			if (Settings::simplifyProjectionByBounds) {
				mPurgedPolys.remove(level, id);
			}
		}
		/// Inserts a polynomial with the given origin into the given level.
		carl::Bitset insertPolynomialTo(std::size_t level, const UPoly& p, const Origin::BaseType& origin, bool setBound = false) {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "Receiving " << p << " for level " << level);
			if (projection::canBeRemoved(p)) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> but is safely removed.");
				return carl::Bitset();
			}
			if ((level < dim()) && projection::canBeForwarded(level, p)) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> but is forwarded to " << (level+1));
				return insertPolynomialTo(level + 1, p.switchVariable(var(level + 1)), origin, setBound);
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "Inserting " << p << " into level " << level);
			assert(level <= dim());
			auto it = mPolynomialIDs[level].find(p);
			if (it != mPolynomialIDs[level].end()) {
				assert(mPolynomials[level][it->second]);
				mPolynomials[level][it->second]->second += origin;
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Polynomial was already present, merged origins");
				return carl::Bitset();
			}
			std::size_t id = getID(level);
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Got new id " << id);
			if (id >= mPolynomials[level].size()) mPolynomials[level].resize(id + 1);
			assert(!mPolynomials[level][id]);
			mPolynomials[level][id] = std::make_pair(p, Origin(origin));
			mLiftingQueues[level - 1].insert(id);
			mPolynomialIDs[level].emplace(p, id);
			if (setBound) {
				mPurgedPolys.setBound(level, id, true);
			}
			if (level < dim()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Inserting " << id << " into queue for level " << (level+1));
				insertIntoProjectionQueue(level, id);
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Done.");
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Now:" << std::endl << *this);
			return carl::Bitset({level});
		}
		/// Removes the polynomial given by the iterator from all datastructures.
		template<typename Iterator>
		Iterator removePolynomialByIT(std::size_t level, Iterator it) {
			assert(it != mPolynomialIDs[level].end());
			std::size_t id = it->second;
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "Removing " << id << " on " << level);
			assert(mPolynomials[level][id]);
			if (level < dim()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Purging from queue on level " << (level+1));
				removeFromProjectionQueue(level, id);
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Removing polynomial");
			mLiftingQueues[level - 1].erase(id);
			mPolynomials[level][id] = boost::none;
			freeID(level, id);
			return mPolynomialIDs[level].erase(it);
		}
		
		carl::Bitset project(const ConstraintSelection&) {
			while (!mProjectionQueue.empty()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting" << std::endl << *this);
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Using next projection candidate " << mProjectionQueue.top());
				QueueEntry qe = mProjectionQueue.top();
				mProjectionQueue.pop();
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Checking if can be purged: " << Settings::simplifyProjectionByBounds);
				if (Settings::simplifyProjectionByBounds && mPurgedPolys.isPurged(qe)) {
					mPurgedPolys.add(qe);
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Purged.");
				} else {
					carl::Bitset res = projectCandidate(qe);
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> res = " << res);
					if (res.any()) return res;
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Projection is finished.");
			return carl::Bitset();
		}
		carl::Bitset projectCandidate(const QueueEntry& qe) {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting " << qe);
			assert(qe.level < dim());
			if (qe.level == 0) {
				assert(qe.first == qe.second);
				assert(mPolynomials[qe.level][qe.first]);
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Moving into level 1: " << mPolynomials[qe.level][qe.first]->first);
				insertPolynomialTo(1, mPolynomials[qe.level][qe.first]->first, Origin::BaseType(qe.level, qe.first));
				return carl::Bitset({1});
			}
			carl::Bitset res;
			if (qe.first == qe.second) {
				assert(qe.first < mPolynomials[qe.level].size());
				assert(mPolynomials[qe.level][qe.first]);
				const auto& p = *mPolynomials[qe.level][qe.first];
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting single " << p << " into " << qe.level);
				mOperator(Settings::projectionOperator, p.first, var(qe.level + 1), 
					[&](const UPoly& np){ res |= insertPolynomialTo(qe.level + 1, np, Origin::BaseType(qe.level, qe.first)); }
				);
			} else {
				assert(qe.first < mPolynomials[qe.level].size());
				assert(qe.second < mPolynomials[qe.level].size());
				assert(mPolynomials[qe.level][qe.first] && mPolynomials[qe.level][qe.second]);
				const auto& p = *mPolynomials[qe.level][qe.first];
				const auto& q = *mPolynomials[qe.level][qe.second];
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting paired " << p << ", " << q << " into " << qe.level);
				mOperator(Settings::projectionOperator, p.first, q.first, var(qe.level + 1), 
					[&](const UPoly& np){ res |= insertPolynomialTo(qe.level + 1, np, Origin::BaseType(qe.level, qe.first, qe.second)); }
				);
			}
			return res;
		}
		
	public:
		Projection(const Constraints& c):
			Super(c),
			mProjectionQueue(ProjectionCandidateComparator([&](std::size_t level, std::size_t id){ return getPolynomialById(level, id); })),
			mPurgedPolys([this](std::size_t level, std::size_t id){
				return canBePurgedByBounds(getPolynomialById(level, id));
			})
		{}
		void reset() {
			Super::reset();
			mPolynomialIDs.clear();
			mPolynomialIDs.resize(dim() + 1);
			mPolynomials.clear();
			mPolynomials.resize(dim() + 1);
			mProjectionQueue.clear();
			mPurgedPolys.reset(dim() + 1);
		}
		carl::Bitset addPolynomial(const UPoly& p, std::size_t cid, bool isBound) override {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Adding " << p << " with id " << cid);
			if (cid >= mPolynomials[0].size()) {
				mPolynomials[0].resize(cid + 1);
			}
			assert(!mPolynomials[0][cid]);
			mPolynomials[0][cid] = std::make_pair(p, Origin());
			mPolynomialIDs[0].emplace(p, cid);
			if (isBound) {
				insertPolynomialTo(1, p, Origin::BaseType(0,cid), true);
			} else {
				mProjectionQueue.emplace(0, cid, cid);
			}
			return carl::Bitset();
		}
		void removePolynomial(const UPoly& p, std::size_t cid, bool isBound) override {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Removing " << cid);
			assert(mPolynomials[0][cid]);
			assert(mPolynomials[0][cid]->first == p);
			mPolynomials[0][cid] = boost::none;
			removeFromProjectionQueue(0, cid);
			carl::Bitset filter = carl::Bitset().set(cid);
			for (std::size_t level = 1; level <= dim(); level++) {
				for (std::size_t lvl = level; lvl <= dim(); lvl++) {
					for (auto it = mPolynomialIDs[level].begin(); it != mPolynomialIDs[level].end(); it++) {
						assert(mPolynomials[level][it->second]);
						mPolynomials[level][it->second]->second.erase(level, filter);
					}
				}
				carl::Bitset removed;
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Purging from level " << level << " with filter " << filter);
				for (auto it = mPolynomialIDs[level].begin(); it != mPolynomialIDs[level].end();) {
					std::size_t id = it->second;
					assert(mPolynomials[level][id]);
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
			if (Settings::simplifyProjectionByBounds && isBound) {
				mPurgedPolys.restore([this](const QueueEntry& qe) {
					mProjectionQueue.push(qe);
				});
			}
		}
		
		std::size_t size(std::size_t level) const override {
			assert(level <= dim());
			return mPolynomialIDs[level].size();
		}
		bool empty(std::size_t level) const override {
			assert(level <= dim());
			return mPolynomialIDs[level].empty();
		}
		
		carl::Bitset projectNewPolynomial(const ConstraintSelection& cs = carl::Bitset(true)) {
			return project(cs);
		}
		
		bool hasPolynomialById(std::size_t level, std::size_t id) const override {
			assert(level <= dim());
			assert(id < mPolynomials[level].size());
			return bool(mPolynomials[level][id]);
		}
		const UPoly& getPolynomialById(std::size_t level, std::size_t id) const override {
			assert(level <= dim());
			assert(id < mPolynomials[level].size());
			assert(mPolynomials[level][id]);
			return mPolynomials[level][id]->first;
		}
		
		void exportAsDot(std::ostream& out) const override {
			mConstraints.exportAsDot(out);
			std::size_t originID = 0;
			for (std::size_t level = 0; level <= dim(); level++) {
				debug::DotSubgraph dsg("level_" + std::to_string(level));
				for (std::size_t id = 0; id < mPolynomials[level].size(); id++) {
					const auto& p = mPolynomials[level][id];
					if (!p) continue;
					out << "\t\tp_" << level << "_" << id << " [label=\"" << p->first << "\"];" << std::endl;
					dsg.add("p_" + std::to_string(level) + "_" + std::to_string(id));
					for (const auto& origin: p->second) {
						std::string target = (origin.level == 0 ? "orig_" : "p_" + std::to_string(origin.level-1) + "_");
						if (origin.first != origin.second) {
							out << "\t\torigin_" << originID << " [label=\"\", shape=point];" << std::endl;
							out << "\t\torigin_" << originID << " -> p_" << level << "_" << id << ";" << std::endl;
							out << "\t\t" << target << origin.first << " -> origin_" << originID << ";" << std::endl;
							out << "\t\t" << target << origin.second << " -> origin_" << originID << ";" << std::endl;
						} else {
							out << "\t\t" << target << origin.first << " -> p_" << level << "_" << id << ";" << std::endl;
						}
						originID++;
					}
				}
				out << "\t" << dsg << std::endl;
			}
		}
		
		Origin getOrigin(std::size_t level, std::size_t id) const override {
			assert(level < mPolynomials.size());
			assert(id < mPolynomials[level].size());
			assert(mPolynomials[level][id]);
			return mPolynomials[level][id]->second;
		}
	};
	
	template<typename S, Backtracking B>
	std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::FULL, B, S>& p) {
		for (std::size_t level = 0; level <= p.dim(); level++) {
			if (level == 0) os << level << std::endl;
			else os << level << " / " << p.var(level) << std::endl;
			os << "\tP: " << p.mPolynomials[level] << std::endl;
			if (level > 0) {
				os << "\tL: " << p.mLiftingQueues[level - 1] << std::endl;
			}
		}
		os << "Q: " << p.mProjectionQueue << std::endl;
		return os;
	}
}
}
