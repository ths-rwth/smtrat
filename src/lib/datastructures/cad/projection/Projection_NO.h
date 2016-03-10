#pragma once

#include <iostream>
#include <map>
#include <vector>

#include "../Common.h"
#include "../utils/DynamicPriorityQueue.h"
#include "BaseProjection.h"

namespace smtrat {
namespace cad {
	
	template<typename Settings>
	class Projection<Incrementality::NONE, Backtracking::ORDERED, Settings>: public BaseProjection {
	private:
		// Maps polynomials to a (per level) unique ID.
		std::vector<std::map<UPoly,std::size_t>> mPolynomialIDs;
		// Stores polynomials with their origin constraint ids.
		std::vector<std::vector<std::pair<UPoly,Bitset>>> mPolynomials;
		
		void addToProjection(std::size_t level, const UPoly& p, const Bitset& origin) {
			if (p.isZero() || p.isNumber()) return;
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Adding " << p << " to projection level " << level);
			assert(level < dim());
			assert(p.mainVar() == var(level));
			auto it = mPolynomialIDs[level].find(p);
			if (it != mPolynomialIDs[level].end()) return;
			if (level < dim() - 1) {
				mOperator(Settings::projectionOperator, p, var(level + 1), 
					[&](const UPoly& np){ addToProjection(level + 1, np, origin); }
				);
				for (const auto& it: mPolynomials[level]) {
					Bitset newOrigin = origin | it.second;
					mOperator(Settings::projectionOperator, p, it.first, var(level + 1),
						[&](const UPoly& np){ addToProjection(level + 1, np, newOrigin); }
					);
				}
			}
			std::size_t newID = mPolynomials[level].size();
			mPolynomials[level].emplace_back(p, origin);
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
		void addPolynomial(const UPoly& p) {
			assert(p.mainVar() == var(0));
			addToProjection(0, p, Bitset().set(mPolynomials[0].size()));
		}
		void removePolynomial(const UPoly& p, const std::function<void(std::size_t,SampleLiftedWith)>& callback) {
			assert(mPolynomials[0].back().first == p);
			mPolynomials[0].pop_back();
			std::size_t cid = mPolynomials[0].size();
			for (std::size_t lvl = 0; lvl < dim(); lvl++) {
				while (mPolynomials[lvl].back().second.test(cid)) {
					auto it = mPolynomialIDs[lvl].find(mPolynomials[lvl].back().first);
					assert(it != mPolynomialIDs[lvl].end());
					mPolynomialIDs[lvl].erase(it);
					mPolynomials[lvl].pop_back();
				}
				callback(lvl, SampleLiftedWith().set(cid));
			}
		}
		
		bool projectNewPolynomial(std::size_t level, const ConstraintSelection& ps = Bitset(true)) {
			return false;
		}
		
		OptionalPoly getPolyForLifting(std::size_t level, SampleLiftedWith& slw) {
			for (const auto& pid: mLiftingQueues[level]) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Checking " << mPolynomials[level][pid].first);
				if (!slw.test(pid)) {
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", mPolynomials[level][pid].first << " can be used.");
					slw.set(pid);
					return OptionalPoly(mPolynomials[level][pid].first);
				} else {
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", mPolynomials[level][pid].first << " was already used.");
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
			return mPolynomials[level][id].first;
		}
		
		template<typename S>
		friend std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::NONE, Backtracking::ORDERED, S>& p) {
			for (std::size_t level = 0; level < p.dim(); level++) {
				os << level << " " << p.var(level) << ":" << std::endl;
				for (const auto& it: p.mPolynomials[level]) {
					os << "\t" << it.first << " [" << it.second << "]" << std::endl;
				}
			}
			return os;
		}
	};
}
}
