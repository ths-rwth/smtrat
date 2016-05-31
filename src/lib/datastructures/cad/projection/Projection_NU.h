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
	class Projection<Incrementality::NONE, Backtracking::UNORDERED, Settings>: public BaseProjection<Settings> {
	private:
		using Super = BaseProjection<Settings>;
		using typename Super::Constraints;
		using Super::mLiftingQueues;
		using Super::mOperator;
		using Super::callRemoveCallback;
		using Super::canBeRemoved;
		using Super::getID;
		using Super::freeID;
		using Super::dim;
		using Super::var;

		template<typename S>
		friend std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::NONE, Backtracking::UNORDERED, S>& p);
		// Maps polynomials to a (per level) unique ID.
		std::vector<std::map<UPoly,std::size_t>> mPolynomialIDs;
		// Stores polynomials with their origins, being pairs of polynomials from the level above.
		std::vector<std::vector<boost::optional<std::pair<UPoly,Origin>>>> mPolynomials;
		
		Bitset addToProjection(std::size_t level, const UPoly& p, const Origin::BaseType& origin) {
			if (canBeRemoved(p)) return Bitset();
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Adding " << p << " to projection level " << level);
			assert(level < dim());
			assert(p.mainVar() == var(level));
			auto it = mPolynomialIDs[level].find(p);
			if (it != mPolynomialIDs[level].end()) {
				assert(mPolynomials[level][it->second]);
				mPolynomials[level][it->second]->second += origin;
				return Bitset();
			}
			std::size_t newID = getID(level);;
			Bitset res;
			if (level < dim() - 1) {
				mOperator(Settings::projectionOperator, p, var(level + 1), 
					[&](const UPoly& np){ res |= addToProjection(level + 1, np, Origin::BaseType(level + 1, newID)); }
				);
				for (const auto& it: mPolynomialIDs[level]) {
					assert(mPolynomials[level][it.second]);
					auto newOrigin = Origin::BaseType(level + 1,newID,it.second);
					mOperator(Settings::projectionOperator, p, it.first, var(level + 1),
						[&](const UPoly& np){ res |= addToProjection(level + 1, np, newOrigin); }
					);
				}
			}
			if (newID >= mPolynomials[level].size()) {
				mPolynomials[level].resize(newID+1);
			}
			mPolynomials[level][newID] = std::make_pair(p, Origin(origin));
			mPolynomialIDs[level].emplace(p, newID);
			mLiftingQueues[level].insert(newID);
			res.set(level);
			return res;
		}
	public:
		Projection(const Constraints& c): Super(c) {}
		void reset() {
			Super::reset();
			mPolynomials.clear();
			mPolynomials.resize(dim());
			mPolynomialIDs.clear();
			mPolynomialIDs.resize(dim());
		}
		Bitset addPolynomial(const UPoly& p, std::size_t cid, bool) {
			assert(p.mainVar() == var(0));
			return addToProjection(0, p, Origin::BaseType(0, cid));
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
						freeID(level, id);
						mLiftingQueues[level].erase(id);
						removed.set(id);
						mPolynomials[level][id] = boost::none;
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
		
		void boundsChanged() {}
		
		std::size_t size(std::size_t level) const {
			return mPolynomialIDs[level].size();
		}
		bool empty(std::size_t level) const {
			return mPolynomialIDs[level].empty();
		}
		
		Bitset projectNewPolynomial(const ConstraintSelection& ps = Bitset(true)) {
			return Bitset();
		}
		
		const UPoly& getPolynomialById(std::size_t level, std::size_t id) const {
			assert(level < mPolynomials.size());
			assert(id < mPolynomials[level].size());
			assert(mPolynomials[level][id]);
			return mPolynomials[level][id]->first;
		}	
	};
	
	template<typename S>
	std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::NONE, Backtracking::UNORDERED, S>& p) {
		for (std::size_t level = 0; level < p.dim(); level++) {
			os << level << " " << p.var(level) << ":" << std::endl;
			for (const auto& it: p.mPolynomialIDs[level]) {
				assert(p.mPolynomials[level][it.second]);
				os << "\t" << it.second << ": " << p.mPolynomials[level][it.second]->first << " " << p.mPolynomials[level][it.second]->second << std::endl;
			}
		}
		return os;
	}
}
}
