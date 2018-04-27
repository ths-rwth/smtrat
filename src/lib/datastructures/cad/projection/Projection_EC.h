#pragma once

#include <iostream>
#include <map>
#include <vector>

#include "../Common.h"
#include "BaseProjection.h"
#include "ProjectionComparator.h"
#include "../../../modules/NewCADModule/NewCADStatistics.h"

namespace smtrat {
namespace cad {
namespace full {
	using Polynomial = boost::optional<std::pair<UPoly,Origin>>;
}
	/*inline std::ostream& operator<<(std::ostream& os, const full::Polynomial& p) {
		if (!p) return os << "--";
		return os << p->first << " " << p->second;
	}*/
	
	template<typename Settings>
	class Projection<Incrementality::FULL, Backtracking::HIDE, Settings>: public BaseProjection<Settings> {
	private:
		using Super = BaseProjection<Settings>;
		using typename Super::Constraints;
		using Super::mConstraints;
		using Super::mLiftingQueues;
		using Super::mOperator;
		using Super::callRemoveCallback;
		using Super::canBeForwarded;
		using Super::canBePurgedByBounds;
		using Super::canBeRemoved;
		using Super::getID;
		using Super::freeID;
		using Super::var;
	public:
		using Super::dim;
		using Super::size;
	private:

#ifdef SMTRAT_DEVOPTION_Statistics
		NewCADStatistics mStatistics;
#endif
		template<typename S>
		friend std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::FULL, Backtracking::HIDE, S>& p);
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
                
                std::vector<carl::Bitset> mBounds;
                std::vector<carl::Bitset> mEvaluated;
                std::vector<carl::Bitset> mPurged;
                std::function<bool(std::size_t,std::size_t)> mCanBePurged; 
                // Stores until which level some polynomials might be (not anymore) purged due to adding / removing bounds.
                std::size_t checkPurged;


		// Maps polynomials to a (per level) unique ID.
		std::vector<std::map<UPoly,std::size_t>> mPolynomialIDs;
		// Stores polynomials with their origins, being pairs of polynomials from the level above.
		std::vector<std::vector<full::Polynomial>> mPolynomials;
		// Stores the projection queue for all candidates.
		PriorityQueue<QueueEntry,ProjectionCandidateComparator> mProjectionQueue;
                // Stores inactive projection queue entries.
                PriorityQueue<QueueEntry,ProjectionCandidateComparator> mInactiveQueue;
                // Stores whether some inactive queue entries might be active again due to adding/removing a polynomial.
                bool updateInactiveQueue;
		
                // inactive polynomials in level 0
                carl::Bitset mInactive; 
                
                
                // Stores IDs of equational constraints for each level 
                std::vector<carl::Bitset> mEqConstraints; 
                // Stores whether an equational constraint is used for restricted projection and which one for each level
                std::vector<std::pair<bool,std::size_t>> mRestricted; 
		
		std::string logPrefix(std::size_t level) const {
			return std::string(dim() - level, '\t');
		}
		
                /*
                 * Evaluate whether a polynomial is purged.
                 * @param level Level of the polnomial.
                 * @param id ID of the polynomial.
                 */
                bool isPurged(std::size_t level, std::size_t id) {
                        assert(level > 0 && level <= dim());
                        SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Checking whether " << level << "/" << id << " is purged.");
                        SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Current bounds are " << mBounds[level]);
                        if (mBounds[level].test(id)) {
                                SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Do not purge as " << level << "/" << id << " is a bound.");
                                return false;
                        }
                        if (mEqConstraints[level].test(id)) {
                                SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Do not purge as " << level << "/" << id << " is an equational constraint.");
                                return false;
                        }
                        if (!mEvaluated[level].test(id)) {
                                SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Checking if " << level << "/" << id << " can be purged.");
                                bool cbp = mCanBePurged(level, id); 
                                mPurged[level].set(id, cbp); 
                                if(cbp) {
                                    carl::Bitset purged = carl::Bitset().set(id);
                                    mLiftingQueues[level - 1].erase(id);
                                    callRemoveCallback(level, purged); 
                                }
                                mEvaluated[level].set(id); 
                        }
                        return mPurged[level].test(id);
                }
                /*
                 * Evaluate whether a queue entry is purged.
                 * @param qe Queue entry.
                 */
                bool isPurged(const QueueEntry& qe) { 
                        if (qe.level == 0) {
                                assert(qe.first == qe.second);
                                return false; //mCanBePurged(0, qe.first);
                        }
                        return isPurged(qe.level, qe.first) || isPurged(qe.level, qe.second); //previously ...level-1
                }
                /*
                 * Evaluates if polynomials are purged, for not yet evaluated polynomials.
                 * @param level Level until which polynomials need to be evaluated.
                 */
                void computePurgedPolynomials(std::size_t level) { 
                    for(std::size_t lvl = 1; lvl <= level; lvl++) { 
                        for(const auto& it: mPolynomialIDs[lvl]) {
                            isPurged(lvl,it.second);
                        }
                    }
#ifdef SMTRAT_DEVOPTION_Statistics
                    std::size_t number = 0;
                    for(std::size_t lvl = 1; lvl <= dim(); lvl++) {
                        number += mPurged[lvl].count();
                    }
                    mStatistics.currentlyPurgedPolynomials(number);
#endif
                }
                
                /*
                 * Returns true when the polynomial is active (if it has an active BaseType and is not purged due to the bounds).
                 * @param level Level of the polynomial.
                 * @param id Id of the polynomial.
                 */
                bool active(std::size_t level, std::size_t id) const {
                    if(level == 0) {
                        return !mInactive.test(id) && !mPurged[0].test(id);
                    } else {
                        return mPolynomials[level][id]->second.isActive() && !mPurged[level].test(id);
                    }
                }
                
		/**
		 * Add projection candidates for a new polynomial.
		 * @param level Level of the projection candidate.
		 * @param id Id of the new polynomial.
		 */
		void insertIntoProjectionQueue(std::size_t level, std::size_t id) {
			assert(level < dim());
                        if(mRestricted[level].first == false) {
                                for (const auto& it: mPolynomialIDs[level]) {
                                        assert(mPolynomials[level][it.second]);
                                        if(!active(level, it.second)) {
                                                mInactiveQueue.emplace(level, it.second, id);
                                        } else {
                                                mProjectionQueue.emplace(level, it.second, id);
                                        }
                                }
                        } else {
                                for (const auto& it: mPolynomialIDs[level]) {
                                        assert(mPolynomials[level][it.second]);
                                        if(it.second == mRestricted[level].second) { 
                                                mProjectionQueue.emplace(level, mRestricted[level].second, id);
                                        //Semi-restricted projection (+ldc)
                                        } else if (Settings::semiRestrictedProjection && it.second == id) {
                                                mProjectionQueue.emplace(level, mRestricted[level].second, id);
                                        } else {
                                                mInactiveQueue.emplace(level, it.second, id);
                                        } 
                                }
                        }
		}
                
                /**
                 * Delete polynomial in mProjection and all other datastructures.
                 * @param p Polynomial in level 0 that is deleted.
                 * @param cid Id of the polynomial in level 0 that is deleted.
                 */
                void deletePolynomials(const UPoly& p, std::size_t cid) {
                        assert(mPolynomials[0][cid]);
			assert(mPolynomials[0][cid]->first == p);
			mPolynomials[0][cid] = boost::none;
                        mProjectionQueue.removeIf([cid](const QueueEntry& qe){ return (qe.level == 0) && (qe.first == cid || qe.second == cid); });
			mInactiveQueue.removeIf([cid](const QueueEntry& qe){ return (qe.level == 0) && (qe.first == cid || qe.second == cid); });
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
                                                SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "Removing " << id << " on " << level);
						if (level < dim()) {
                                                        mProjectionQueue.removeIf([level,id](const QueueEntry& qe){ return (qe.level == level) && (qe.first == id || qe.second == id); });
                                                        mInactiveQueue.removeIf([level,id](const QueueEntry& qe){ return (qe.level == level) && (qe.first == id || qe.second == id); });
                                                }
                                                SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Removing polynomial");
                                                mLiftingQueues[level - 1].erase(id);
                                                mPolynomials[level][id] = boost::none;
                                                freeID(level, id);
                                                it = mPolynomialIDs[level].erase(it);    
					} else {
						it++;
					}
				}
				SMTRAT_LOG_TRACE("smtrat.cad.projection", "Calling callback for level " << level << ", removed [" << removed << "]");
				callRemoveCallback(level, removed);
				filter = removed;
			}
                }
                /**
                 * Deactivate inactive polynomials in mProjection.
                 * @param level Level at which first deactivation occured.
                 */
                void deactivatePolynomials(std::size_t level) {
                        for (std::size_t lvl = level; lvl < dim(); lvl++) {
                                // find inactive polynomials in lvl
                                carl::Bitset remove;
				for (const auto& it: mPolynomialIDs[lvl]) {
					std::size_t id = it.second;
					assert(mPolynomials[lvl][id]);
					if (!active(lvl, id)) {
						SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Purging " << id << " from level " << lvl);
						remove.set(id);
					} 
				}
				SMTRAT_LOG_TRACE("smtrat.cad.projection", "Calling callback for level " << level << ", removed [" << remove << "]");
				if(lvl > 0) {
					callRemoveCallback(lvl, remove);
				}
                                // deactivate polynomials in following levels due to the inactive polynomials in lvl
				for (std::size_t l = lvl+1; l <= dim(); l++) {
					for (const auto& it: mPolynomialIDs[l]) {
						assert(mPolynomials[l][it.second]);
						mPolynomials[l][it.second]->second.deactivate(lvl, remove);
						// remove inactive polynomials from LiftingQueue
						if(!active(l,it.second)) {
							mLiftingQueues[l-1].erase(it.second);
						}
					}
				}
			} 
                }
                /**
                 * Activate active polynomials in mProjection.
                 * @param level Level at which first activation occured.
                 */
                carl::Bitset activatePolynomials(std::size_t level) {
						carl::Bitset changed_levels;
                        for (std::size_t lvl = level; lvl < dim(); lvl++) {
                                // find active polynomials in lvl
                                carl::Bitset activate;
				for (const auto& it: mPolynomialIDs[lvl]) {
					std::size_t id = it.second;
					assert(mPolynomials[lvl][id]);
					if (active(lvl, id)) {
						SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> " << id << " from level " << lvl << " is active");
						activate.set(id);
						changed_levels.set(lvl);
					} else {
						SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> " << id << " from level " << lvl << " remains inactive");
					}
				}
                                // activate polynomials in following levels due to the active polynomials in lvl
				for (std::size_t l = lvl+1; l <= dim(); l++) {
					for (const auto& it: mPolynomialIDs[l]) {
						assert(mPolynomials[l][it.second]);
						SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Activating origins for " << it.second << " from level " << lvl << " with " << activate);
						mPolynomials[l][it.second]->second.activate(lvl, activate);
						//add active polynomials to LiftingQueue
						if(active(l,it.second)) {
							mLiftingQueues[l-1].insert(it.second);
						}
					}
				}
			} 
                        updateInactiveQueue = true;
		return changed_levels;
                }
                
                /**
		 * Deactivate polynomials in the projection (in lvl > level) that become irrelevant due to a new equational constraint.
		 * @param level Level of the equational constraint.
		 */ 
		void restrictProjection(std::size_t level) {
                        std::size_t lvl = level;
                        bool restricted = false;
                        while(lvl < dim() && mRestricted[lvl].first == false && mEqConstraints[lvl].any() && (Settings::interruptions || mRestricted[lvl-1].first == true)){ 
#ifdef SMTRAT_DEVOPTION_Statistics
                            mStatistics.usedRestrictedProjection();
#endif
                            restricted = true;
                            mRestricted[lvl].first = true;
                            mRestricted[lvl].second = mEqConstraints[lvl].find_first(); 
                            carl::Bitset eqc = carl::Bitset().set(mEqConstraints[lvl].find_first()); 
                            for(std::size_t l = lvl + 1; l <= dim(); l++) {
                                for (const auto& it: mPolynomialIDs[l]) {
                                        assert(mPolynomials[l][it.second]);
                                        mPolynomials[l][it.second]->second.deactivateEC(lvl, eqc);
					if(!active(l,it.second)) {
						mLiftingQueues[l-1].erase(it.second);
					}
                                }
                            }
                            lvl++;
                        }
                        if(restricted) {
                            deactivatePolynomials(level+1);
                        }
		}
                /**
		 * Activate polynomials in the projection (in lvl > level) that become again relevant if an equational constraint is removed. 
                 * (Extend restricted projection if necessary.)
		 * @param p Polynomial that becomes removed.
		 */
                void extendProjection(const UPoly& p) {
                        std::size_t level = 1;
                        while((level < dim()) && canBeForwarded(level, p.switchVariable(var(level)))){
                                level += 1;
                        }
                        if(mPolynomialIDs[level].find(p.switchVariable(var(level))) == mPolynomialIDs[level].end()) {
				return;
			}
                        std::size_t id = mPolynomialIDs[level].find(p.switchVariable(var(level)))->second;
                        mEqConstraints[level].reset(id);
                        if(!mRestricted[level].first || id != mRestricted[level].second) {
                            return; 
                        }
                        if(mEqConstraints[level].none()) { 
                                std::size_t lvl = level;
                                carl::Bitset eqc;
                                while(lvl == level || (mRestricted[lvl].first == true && !Settings::interruptions)){
                                        mRestricted[lvl].first = false;
                                        eqc = carl::Bitset().set(mRestricted[lvl].second);
                                        for (std::size_t l = lvl + 1; l <= dim(); l++) {
                                            for (const auto& it: mPolynomialIDs[l]) {
                                                    assert(mPolynomials[l][it.second]);
                                                    mPolynomials[l][it.second]->second.activateEC(lvl, eqc);
						    if(active(l,it.second)) {
							    mLiftingQueues[l-1].insert(it.second);
						    }
                                            }
                                        }
                                        lvl++;
                                }
                                activatePolynomials(level+1);
                        } else {
                                mRestricted[level].first = false;
                                carl::Bitset eqc;
                                eqc = carl::Bitset().set(id);
                                for (std::size_t l = level + 1; l <= dim(); l++) {
                                    for (const auto& it: mPolynomialIDs[l]) {
                                            assert(mPolynomials[l][it.second]);
                                            mPolynomials[l][it.second]->second.activateEC(level, eqc);
					    if(active(l,it.second)) {
						    mLiftingQueues[l-1].insert(it.second);
					    }
                                    }
                                }         
                                activatePolynomials(level+1);
                                restrictProjection(level);
                        }    
                }
                
		/// Inserts a polynomial with the given origin into the given level.
		carl::Bitset insertPolynomialTo(std::size_t level, const UPoly& p, const Origin::BaseType& origin, bool setBound = false, bool isEqC = false) {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "Receiving " << p << " for level " << level);
			if (canBeRemoved(p)) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> but is safely removed.");
				return carl::Bitset();
			}
			if ((level < dim()) && canBeForwarded(level, p)) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> but is forwarded to " << (level+1));
				return insertPolynomialTo(level + 1, p.switchVariable(var(level + 1)), origin, setBound, isEqC);
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "Inserting " << p << " into level " << level);
			assert(level <= dim());
			auto it = mPolynomialIDs[level].find(p);
			if (it != mPolynomialIDs[level].end()) {
				assert(mPolynomials[level][it->second]); 
				if (Settings::simplifyProjectionByBounds && setBound) {
                                assert(level > 0 && level <= dim());
                                SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Setting " << level << "/" << it->second << " is a bound.");
                                mBounds[level].set(it->second);
				}
                                bool activated = active(level,it->second);
				mPolynomials[level][it->second]->second += origin;
                                // in case p was inactive but becomes active by new BaseType activate successors
                                if(activated == false && active(level,it->second)) {
                                    activatePolynomials(level);
				    mLiftingQueues[level-1].insert(it->second); 
                                    updateInactiveQueue = true; 
                                }
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
			if (Settings::simplifyProjectionByBounds && setBound) {
                                assert(level > 0 && level <= dim());
                                SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Setting " << level << "/" << id << " is a bound.");
                                mBounds[level].set(id);
			}
			if (level < dim()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Inserting " << id << " into queue for level " << (level+1));
				insertIntoProjectionQueue(level, id);
			}
                        if(Settings::restrictProjectionByEC && isEqC) { 
                                mEqConstraints[level].set(id); 
                                restrictProjection(level);
                        }
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(level) << "-> Done.");
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Now:" << std::endl << *this);
			return carl::Bitset({level});
		}
		
		carl::Bitset project(const ConstraintSelection&) {
			while (!mProjectionQueue.empty()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting" << std::endl << *this);
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Using next projection candidate " << mProjectionQueue.top());
				QueueEntry qe = mProjectionQueue.top();
				mProjectionQueue.pop();
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Checking if can be purged: " << Settings::simplifyProjectionByBounds);
				if (Settings::simplifyProjectionByBounds && isPurged(qe)) {
					mInactiveQueue.push(qe); 
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> Purged.");
                                } else if(!active(qe.level, qe.first) || !active(qe.level, qe.second)) {
                                        mInactiveQueue.push(qe); 
                                } else if(Settings::restrictProjectionByEC && qe.level != 0 && mRestricted[qe.level].first == true && (qe.first != mRestricted[qe.level].second && qe.second != mRestricted[qe.level].second)) {
                                        mInactiveQueue.push(qe); 
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
#ifdef SMTRAT_DEVOPTION_Statistics
                        mStatistics.computePolynomial();
#endif
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
                                bool isEqC = false;
                                if(mEqConstraints[qe.level].test(qe.first) && mEqConstraints[qe.level].test(qe.second)) {
                                    isEqC = true;
                                }                                
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Projecting paired " << p << ", " << q << " into " << qe.level);
				mOperator(Settings::projectionOperator, p.first, q.first, var(qe.level + 1), 
					[&](const UPoly& np){ res |= insertPolynomialTo(qe.level + 1, np, Origin::BaseType(qe.level, qe.first, qe.second), false, isEqC); }
				);
			}
			return res;
		}
		
	public:
		Projection(const Constraints& c):
			Super(c),
			mCanBePurged([this](std::size_t level, std::size_t id){
				return canBePurgedByBounds(getPolynomialById(level, id));
			}),
			mProjectionQueue(ProjectionCandidateComparator([&](std::size_t level, std::size_t id){ return getPolynomialById(level, id); })),
			mInactiveQueue(ProjectionCandidateComparator([&](std::size_t level, std::size_t id){ return getPolynomialById(level, id); }))
#ifdef SMTRAT_DEVOPTION_Statistics
                        ,mStatistics("CAD")
#endif
		{}
		void reset() {
			Super::reset();
			mPolynomialIDs.clear();
			mPolynomialIDs.resize(dim() + 1);
			mPolynomials.clear();
			mPolynomials.resize(dim() + 1);
			mProjectionQueue.clear();
                        mInactiveQueue.clear();
                        
                        mBounds.clear();
                        mBounds.resize(dim() + 1);
                        mEvaluated.clear();
                        mEvaluated.resize(dim() + 1);
                        mPurged.clear();
                        mPurged.resize(dim() + 1);
                        
                        mEqConstraints.clear();
                        mEqConstraints.resize(dim() + 1);
                        mRestricted.clear();
                        mRestricted.resize(dim()+ 1);
                        mRestricted[0].first = true;
                        for(std::size_t i = 1; i <= dim(); i++) {
                            mRestricted[i].first = false;
                        }
                        updateInactiveQueue = false;
                        checkPurged = 0;
		}
		carl::Bitset addPolynomial(const UPoly& p, std::size_t cid, bool isBound) override {
			if (cid >= mPolynomials[0].size()) {
				mPolynomials[0].resize(cid + 1);
			} else if (mPolynomials[0][cid]) { 
                                mInactive.reset(cid); 
                                // activate all successors of p
                                activatePolynomials(0);
                                if(Settings::simplifyProjectionByBounds && isBound) { 
                                    mEvaluated[0] &= mPurged[0];
                                    std::size_t level = 1; 
                                    while (level < dim()) {
                                        mEvaluated[level] &= mPurged[level];
										if (!canBeForwarded(level, p.switchVariable(var(level)))) break;
                                        level += 1;
                                    }
                                    checkPurged = std::max(level, checkPurged);
                                } 
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(0) << "-> Polynomial was already present, reactivated");
				return carl::Bitset(); 
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Adding " << p << " with id " << cid);
			assert(!mPolynomials[0][cid]);
			mPolynomials[0][cid] = std::make_pair(p, Origin());
			mPolynomialIDs[0].emplace(p, cid); 
			if (Settings::simplifyProjectionByBounds && isBound) { 
                                insertPolynomialTo(1, p, Origin::BaseType(0,cid), true, false);
                                std::size_t level = 1;
                                while (level < dim()) {
                                    mEvaluated[level] &= mPurged[level];
									if (!canBeForwarded(level, p.switchVariable(var(level)))) break;
                                    level += 1;
                                }
                                checkPurged = std::max(level, checkPurged);
			} else {
				mProjectionQueue.emplace(0, cid, cid);
			}
			return carl::Bitset();
		}
                carl::Bitset addEqConstraint(const UPoly& p, std::size_t cid, bool isBound) override {
#ifdef SMTRAT_DEVOPTION_Statistics
    mStatistics.addedECtoCAD();
#endif
                        if (cid >= mPolynomials[0].size()) {
				mPolynomials[0].resize(cid + 1);
			} else if (mPolynomials[0][cid]) { 
                                std::size_t level = 1;
                                while (level < dim()) {
                                    if (Settings::simplifyProjectionByBounds && isBound) {
                                        mEvaluated[level] &= mPurged[level];
                                    }
									if (!canBeForwarded(level, p.switchVariable(var(level)))) break;
                                    level += 1;
                                }
                                if (Settings::simplifyProjectionByBounds && isBound) { 
                                        checkPurged = std::max(level, checkPurged);
                                }
                                auto itp = mPolynomialIDs[level].find(p.switchVariable(var(level)));
                                if(Settings::restrictProjectionByEC) {
                                    mEqConstraints[level].set(itp->second); 
                                    mPurged[level].reset(itp->second);
				    restrictProjection(level);
                                }
				mInactive.reset(cid);
				activatePolynomials(0);
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", logPrefix(0) << "-> Polynomial was already present, reactivated");
				return carl::Bitset(); 
			}    
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Adding " << p << " with id " << cid);
			assert(!mPolynomials[0][cid]);
			mPolynomials[0][cid] = std::make_pair(p, Origin());
			mPolynomialIDs[0].emplace(p, cid);
			insertPolynomialTo(1, p, Origin::BaseType(0,cid), isBound, true);
                        if (Settings::simplifyProjectionByBounds && isBound) { 
                                std::size_t level = 1;
                                while (level < dim()) {
                                    mEvaluated[level] &= mPurged[level];
									if (!canBeForwarded(level, p.switchVariable(var(level)))) break;
                                    level += 1;
                                }
                                checkPurged = std::max(level, checkPurged);
			}
                        return carl::Bitset();
		}
		void removePolynomial(const UPoly& p, std::size_t cid, bool isBound) override {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Removing " << cid);
			assert(mPolynomials[0][cid]);
			assert(mPolynomials[0][cid]->first == p);
                        mInactive.set(cid);
                        // activates polynomials that were inactive due to p, if p is an equational polynomial
                        if(Settings::restrictProjectionByEC) {
                            extendProjection(p);
                        }
                        if(Settings::deletePolynomials) {
                            deletePolynomials(p, cid);
                        } else {
                            // deactivates all successors of p   
                            deactivatePolynomials(0);
                        }
			if (Settings::simplifyProjectionByBounds && isBound) {
                                updateInactiveQueue = true;  
                                std::size_t level = 1;
                                while (level < dim()) {
                                    mEvaluated[level] -= mPurged[level];
									if (!canBeForwarded(level, p.switchVariable(var(level)))) break;
                                    level += 1;
                                }
                                checkPurged = std::max(level, checkPurged);
			}
		}
		
		std::size_t size(std::size_t level) const override {
			assert(level <= dim());
                        std::size_t number = 0;
                        for (const auto& it: mPolynomialIDs[level]) {
                                assert(mPolynomials[level][it.second]);
                                if(active(level,it.second)) {
                                    number += 1;
                                }
                        }
			return number;
		}
		bool empty(std::size_t level) const override {
			assert(level <= dim());
			return mPolynomialIDs[level].empty();
		}
		
		carl::Bitset projectNewPolynomial(const ConstraintSelection& cs = carl::Bitset(true)) {
                        if(updateInactiveQueue) {
                            // activate all QE that became relevant again 
                            for (auto it = mInactiveQueue.begin(); it != mInactiveQueue.end(); ) { 
                                if(active(it->level, it->first) && active(it->level, it->second)) {
                                    if(mRestricted[it->level].first != true || it->level == 0) {
                                        mProjectionQueue.push((*it));
                                        it = mInactiveQueue.erase(it);
                                    } else if(Settings::restrictProjectionByEC && mRestricted[it->level].first == true && (it->first == mRestricted[it->level].second || it->second == mRestricted[it->level].second)){
                                        mProjectionQueue.push((*it)); 
                                        it = mInactiveQueue.erase(it);
                                    } else {
                                        it++;
                                    }
                                } else {
                                    it++;
                                }
                            }
                            mInactiveQueue.fix();
                            updateInactiveQueue = false;
                        }
                        if(checkPurged > 0) {
                            SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> ComputePurgedPolynomials, until level " << checkPurged);
                            computePurgedPolynomials(checkPurged);
                            deactivatePolynomials(1);
                            carl::Bitset levels = activatePolynomials(1);
                            checkPurged = 0;
							if (levels.any()) return levels;
                        }
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
	
	template<typename S>
	std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::FULL, Backtracking::HIDE, S>& p) {
		for (std::size_t level = 0; level <= p.dim(); level++) {
			if (level == 0) os << level << std::endl;
			else os << level << " / " << p.var(level) << std::endl;
			os << "\tP: " << p.mPolynomials[level] << " (purged " << p.mPurged[level] << " / " << p.mEvaluated[level] << ")(ec " << p.mEqConstraints[level] << ")" << std::endl;
			if (level > 0) {
				os << "\tL: " << p.mLiftingQueues[level - 1] << std::endl;
			}
		}
		os << "Q: " << p.mProjectionQueue << std::endl;
		return os;
	}
}
}
