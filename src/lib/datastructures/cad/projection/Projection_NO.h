#pragma once

#include <iostream>
#include <map>
#include <vector>

#include "../Common.h"
#include "BaseProjection.h"

namespace smtrat {
namespace cad {
	
	/**
	 * This class implements a projection that supports no incrementality and expects backtracking to be in order.
	 *
	 * It is based on the following data structures:
	 * - mPolynomialIDs: maps polynomials to a (per level) unique id
	 * - mPolynomials: stores polynomials as a list (per level) with their origin
	 *
	 * The origin of a polynomial in level zero is the id of the corresponding constraint.
	 * For all other levels, it is the id of some polynomial from level zero such that the polynomial must be removed if the origin is removed.
	 * For a single projection operation, the resulting origin is the largest of the participating polynomials.
	 * If a polynomial is derived from multiple projection operations, the origin is the earliest and thus smallest, at least for this non-incremental setting.
	 */
	template<typename Settings>
	class Projection<Incrementality::NONE, Backtracking::ORDERED, Settings>: public BaseProjection<Settings> {
	private:
		using Super = BaseProjection<Settings>;
		using typename Super::Constraints;
		using Super::mLiftingQueues;
		using Super::mOperator;
		using Super::callRemoveCallback;
		using Super::canBeRemoved;
		using Super::canBeForwarded;
		using Super::var;
	public:
		using Super::dim;
		using Super::size;
	private:
		
		template<typename S>
		friend std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::NONE, Backtracking::ORDERED, S>& p);
		/// Maps polynomials to a (per level) unique ID.
		std::vector<std::map<UPoly,std::size_t>> mPolynomialIDs;
		/// Stores polynomials with their origin constraint ids.
		std::vector<std::vector<std::pair<UPoly,std::size_t>>> mPolynomials;
		
		auto& polyIDs(std::size_t level) {
			assert(level > 0 && level <= dim());
			return mPolynomialIDs[level - 1];
		}
		const auto& polyIDs(std::size_t level) const {
			assert(level > 0 && level <= dim());
			return mPolynomialIDs[level - 1];
		}
		auto& polys(std::size_t level) {
			assert(level > 0 && level <= dim());
			return mPolynomials[level - 1];
		}
		const auto& polys(std::size_t level) const {
			assert(level > 0 && level <= dim());
			return mPolynomials[level - 1];
		}
		
		/// Inserts a polynomial with the given origin into the given level.
		void insertPolynomial(std::size_t level, const UPoly& p, std::size_t origin) {
			assert(level > 0 && level <= dim());
			assert(polyIDs(level).find(p) == polyIDs(level).end());
			std::size_t id = polys(level).size();
			polys(level).emplace_back(p, origin);
			polyIDs(level).emplace(p, id);
			mLiftingQueues[level - 1].insert(id);
		}
		/// Removed the last polynomial from the given level.
		void removePolynomial(std::size_t level) {
			assert(level > 0 && level <= dim());
			auto it = polyIDs(level).find(polys(level).back().first);
			assert(it != polyIDs(level).end());
			mLiftingQueues[level - 1].erase(it->second);
			polyIDs(level).erase(it);
			polys(level).pop_back();
		}
		
		/// Adds a new polynomial to the given level and perform the projection recursively.
		carl::Bitset addToProjection(std::size_t level, const UPoly& p, std::size_t origin) {
			assert(level > 0 && level <= dim());
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Adding " << p << " to projection level " << level);
			if (canBeRemoved(p)) return carl::Bitset();
			if (level < dim() && canBeForwarded(level, p)) {
				return addToProjection(level + 1, p.switchVariable(var(level+1)), origin);
			}
			assert(p.mainVar() == var(level));
			auto it = polyIDs(level).find(p);
			if (it != polyIDs(level).end()) {
				// We already have this polynomial.
				if (level > 0) {
					assert(polys(level)[it->second].second <= origin);
				}
				return carl::Bitset();
			}
			carl::Bitset res;
			if (level < dim()) {
				mOperator(Settings::projectionOperator, p, var(level + 1), 
					[&](const UPoly& np){ res |= addToProjection(level + 1, np, origin); }
				);
				for (const auto& it: polys(level)) {
					std::size_t newOrigin = std::max(origin, it.second);
					mOperator(Settings::projectionOperator, p, it.first, var(level + 1),
						[&](const UPoly& np){ res |= addToProjection(level + 1, np, newOrigin); }
					);
				}
			}
			// Actually insert afterwards to avoid pairwise projection with itself.
			insertPolynomial(level, p, origin);
			res.set(level);
			return res;
		}
	public:
		Projection(const Constraints& c): Super(c) {}
		/**
		 * Resets all datastructures, use the given variables from now on.
		 */
		void reset() {
			Super::reset();
			mPolynomials.clear();
			mPolynomials.resize(dim());
			mPolynomialIDs.clear();
			mPolynomialIDs.resize(dim());
		}
		/**
		 * Adds the given polynomial to the projection with the given constraint id as origin.
		 * Asserts that the main variable of the polynomial is the first variable.
		 */
		carl::Bitset addPolynomial(const UPoly& p, std::size_t cid, bool) override {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Adding " << p << " from constraint " << cid);
			assert(p.mainVar() == var(1));
			return addToProjection(1, p, cid);
		}
		/**
		 * Removed the given polynomial from the projection.
		 * Asserts that this polynomial was the one added last and has the given constraint id as origin.
		 * Calls the callback function for every level with a mask designating the polynomials removed from this level.
		 */
		void removePolynomial(const UPoly& p, std::size_t cid, bool) override {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Removing " << p << " from constraint " << cid);
			// Remove all polynomials from all levels that have the removed constraint as origin.
			for (std::size_t level = 1; level <= dim(); level++) {
				carl::Bitset removed;
				if (polys(level).empty()) continue;
				while (polys(level).back().second == cid) {
					std::size_t id = polys(level).size() - 1;
					mLiftingQueues[level - 1].erase(id);
					removePolynomial(level);
					removed.set(id);
				}
				assert(polys(level).empty() || polys(level).back().second < cid);
				callRemoveCallback(level, removed);
			}
		}
		
		/// Returns the number of polynomials in this level.
		std::size_t size(std::size_t level) const override {
			return polys(level).size();
		}
		/// Returns whether the number of polynomials in this level is zero.
		bool empty(std::size_t level) const override {
			return polys(level).empty();
		}
		
		/// Returns false, as the projection is not incremental.
		carl::Bitset projectNewPolynomial(const ConstraintSelection& = carl::Bitset(true)) {
			return carl::Bitset();
		}
		bool hasPolynomialById(std::size_t level, std::size_t id) const override {
			assert(level > 0 && level <= dim());
			return id < polys(level).size();
		}
		/// Get the polynomial from this level with the given id.
		const UPoly& getPolynomialById(std::size_t level, std::size_t id) const override {
			assert(level > 0 && level <= dim());
			assert(id < polys(level).size());
			return polys(level)[id].first;
		}
	};
	
	template<typename S>
	std::ostream& operator<<(std::ostream& os, const Projection<Incrementality::NONE, Backtracking::ORDERED, S>& p) {
		for (std::size_t level = 1; level <= p.dim(); level++) {
			os << level << " / " << p.var(level) << ":" << std::endl;
			for (const auto& it: p.polys(level)) {
				os << "\t" << it.first << " [" << it.second << "]" << std::endl;
			}
		}
		return os;
	}
}
}
