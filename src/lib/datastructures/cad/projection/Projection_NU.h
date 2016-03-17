#pragma once

#include <iostream>
#include <map>
#include <vector>

#include <boost/optional.hpp>

#include "../Common.h"
#include "BaseProjection.h"

namespace smtrat {
namespace cad {
	
	/**
	 * This class implements a projection that supports no incrementality and allows backtracking to be out of order.
	 */
	template<typename Settings>
	class Projection<Incrementality::NONE, Backtracking::UNORDERED, Settings>: public BaseProjection {
	private:
		// Maps polynomials to a (per level) unique ID.
		std::vector<std::map<UPoly,std::size_t>> mPolynomialIDs;
		// Stores polynomials with their origins, being pairs of polynomials from the level above.
		std::vector<std::vector<boost::optional<std::pair<UPoly,Origin>>>> mPolynomials;
		
		void addToProjection(std::size_t level, const UPoly& p, const Origin::BaseType& origin) {
			if (p.isZero() || p.isNumber()) return;
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Adding " << p << " to projection level " << level);
			assert(level < dim());
			assert(p.mainVar() == var(level));
			auto it = mPolynomialIDs[level].find(p);
			if (it != mPolynomialIDs[level].end()) {
				assert(mPolynomials[level][it->second]);
				mPolynomials[level][it->second]->second += origin;
				return;
			}
			std::size_t newID = mIDPools[level].get();
			if (level < dim() - 1) {
				mOperator(Settings::projectionOperator, p, var(level + 1), 
					[&](const UPoly& np){ addToProjection(level + 1, np, Origin::BaseType(newID)); }
				);
				for (const auto& it: mPolynomialIDs[level]) {
					assert(mPolynomials[level][it.second]);
					auto newOrigin = Origin::BaseType(newID,it.second);
					mOperator(Settings::projectionOperator, p, it.first, var(level + 1),
						[&](const UPoly& np){ addToProjection(level + 1, np, newOrigin); }
					);
				}
			}
			if (newID >= mPolynomials[level].size()) {
				mPolynomials[level].resize(newID+1);
			}
			mPolynomials[level][newID] = std::make_pair(p, Origin(origin));
			mPolynomialIDs[level].emplace(p, newID);
			mLiftingQueues[level].insert(newID);
		}
	public:
		void reset(const std::vector<carl::Variable>& vars) {
			BaseProjection::reset(vars);
			mPolynomials.clear();
			mPolynomials.resize(dim());
			mPolynomialIDs.clear();
			mPolynomialIDs.resize(dim());
		}
		void addPolynomial(const UPoly& p, std::size_t cid) {
			assert(p.mainVar() == var(0));
			addToProjection(0, p, Origin::BaseType(cid));
		}
		void removePolynomial(const UPoly& p, std::size_t cid) {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Removing " << cid);
			Bitset filter = Bitset().set(cid);
			for (std::size_t level = 0; level < dim(); level++) {
				Bitset removed;
				for (auto it = mPolynomialIDs[level].begin(); it != mPolynomialIDs[level].end();) {
					std::size_t id = it->second;
					assert(mPolynomials[level][id]);
					mPolynomials[level][id]->second -= filter;
					if (mPolynomials[level][id]->second.empty()) {
						mIDPools[level].free(id);
						removed.set(id);
						mLiftingQueues[level].erase(id);
						it = mPolynomialIDs[level].erase(it);
						mPolynomials[level][id] = boost::none;
					} else {
						it++;
					}
				}
				SMTRAT_LOG_TRACE("smtrat.cad.projection", "Calling callback for level " << level << ", removed [" << removed << "]");
				mRemoveCallback(level, removed);
				filter = removed;
			}
		}
		
		std::size_t size(std::size_t level) const {
			return mPolynomialIDs[level].size();
		}
		bool empty(std::size_t level) const {
			return mPolynomialIDs[level].empty();
		}
		
		bool projectNewPolynomial(std::size_t level, const ConstraintSelection& ps = Bitset(true)) {
			return false;
		}
		
		OptionalPoly getPolyForLifting(std::size_t level, SampleLiftedWith& slw) {
			for (const auto& pid: mLiftingQueues[level]) {
				assert(mPolynomials[level][pid]);
				SMTRAT_LOG_TRACE("smtrat.cad.projection", "Checking " << mPolynomials[level][pid]->first);
				if (!slw.test(pid)) {
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", mPolynomials[level][pid]->first << " can be used.");
					slw.set(pid);
					return OptionalPoly(mPolynomials[level][pid]->first);
				} else {
					SMTRAT_LOG_TRACE("smtrat.cad.projection", mPolynomials[level][pid]->first << " was already used.");
				}
			}
			return OptionalPoly();
		}
		OptionalPoly getPolyForLifting(std::size_t level, SampleLiftedWith& slw, const ConstraintSelection& cs) {
			for (const auto& pid: mLiftingQueues[level]) {
				if (!slw.test(pid)) {
					if ((mPolynomials[level][pid].second & cs).any()) {
						slw.set(pid);
						return OptionalPoly(mPolynomials[level][pid].first);
					}
				}
			}
			return OptionalPoly();
		}
		
		const UPoly& getPolynomialById(std::size_t level, std::size_t id) const {
			assert(level < mPolynomials.size());
			assert(id < mPolynomials[level].size());
			assert(mPolynomials[level][id]);
			return mPolynomials[level][id]->first;
		}
		
		template<typename S>
		friend std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::NONE, Backtracking::UNORDERED, S>& p) {
			for (std::size_t level = 0; level < p.dim(); level++) {
				os << level << " " << p.var(level) << ":" << std::endl;
				for (const auto& it: p.mPolynomialIDs[level]) {
					assert(p.mPolynomials[level][it.second]);
					os << "\t" << it.second << ": " << p.mPolynomials[level][it.second]->first << " " << p.mPolynomials[level][it.second]->second << std::endl;
				}
			}
			return os;
		}
	};
}
}
