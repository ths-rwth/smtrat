#pragma once

#include <iostream>
#include <map>
#include <vector>

#include <boost/optional.hpp>

#include <lib/datastructures/cad/Common.h>
#include <lib/datastructures/cad/projection/BaseProjection.h>

namespace smtrat::qe::cad {

	using smtrat::cad::BaseProjection;
	using smtrat::cad::Origin;
	using smtrat::cad::UPoly;

	template<typename Settings>
	class Projection: public BaseProjection<Settings> {
	private:
		using Super = BaseProjection<Settings>;
		using typename Super::Constraints;
		using Super::mLiftingQueues;
		using Super::mOperator;
		using Super::callRemoveCallback;
		using Super::getID;
		using Super::freeID;
		using Super::var;
	public:
		using Super::dim;
		using Super::size;

	private:
		template<typename S>
		friend std::ostream& operator<<(std::ostream& os, const Projection<S>& p);

		std::vector<std::map<UPoly,std::size_t>> mPolynomialIDs;
		std::vector<std::vector<boost::optional<std::pair<UPoly,Origin>>>> mPolynomials;

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

		carl::Bitset addToProjection(std::size_t level, const UPoly& p, const Origin::BaseType& origin) {
			assert(level > 0 && level <= dim());
			if (smtrat::cad::projection::canBeRemoved(p)) return carl::Bitset();
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Adding " << p << " to projection level " << level);
			assert(p.mainVar() == var(level));
			auto it = polyIDs(level).find(p);
			if (it != polyIDs(level).end()) {
				assert(polys(level)[it->second]);
				polys(level)[it->second]->second += origin;
				return carl::Bitset();
			}
			std::size_t newID = getID(level);;
			carl::Bitset res;
			if (level < dim()) {
				mOperator(Settings::projectionOperator, p, var(level + 1),
					[&](const UPoly& np){ res |= addToProjection(level + 1, np, Origin::BaseType(level, newID)); }
				);
				for (const auto& it: polyIDs(level)) {
					assert(polys(level)[it.second]);
					auto newOrigin = Origin::BaseType(level, newID, it.second);
					mOperator(Settings::projectionOperator, p, it.first, var(level + 1),
						[&](const UPoly& np){ res |= addToProjection(level + 1, np, newOrigin); }
					);
				}
			}
			if (newID >= polys(level).size()) {
				polys(level).resize(newID + 1);
			}
			polys(level)[newID] = std::make_pair(p, Origin(origin));
			polyIDs(level).emplace(p, newID);
			mLiftingQueues[level - 1].insert(newID);
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

		carl::Bitset addPolynomial(const UPoly& p, std::size_t cid, bool) override {
			assert(p.mainVar() == var(1));
			return addToProjection(1, p, Origin::BaseType(0, cid));
		}
		void removePolynomial(const UPoly&, std::size_t cid, bool) override {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Removing " << cid);
			carl::Bitset filter = carl::Bitset().set(cid);
			for (std::size_t level = 1; level <= dim(); level++) {
				for (std::size_t lvl = level; lvl <= dim(); lvl++) {
					for (auto it = polyIDs(level).begin(); it != polyIDs(level).end(); it++) {
						assert(polys(level)[it->second]);
						polys(level)[it->second]->second.erase(level, filter);
					}
				}
				carl::Bitset removed;
				for (auto it = polyIDs(level).begin(); it != polyIDs(level).end();) {
					std::size_t id = it->second;
					assert(polys(level)[id]);
					if (polys(level)[id]->second.empty()) {
						freeID(level, id);
						mLiftingQueues[level - 1].erase(id);
						removed.set(id);
						polys(level)[id] = boost::none;
						it = polyIDs(level).erase(it);
					} else {
						it++;
					}
				}
				SMTRAT_LOG_TRACE("smtrat.cad.projection", "Calling callback for level " << level << ", removed [" << removed << "]");
				callRemoveCallback(level, removed);
				filter = removed;
			}
    }

		bool testProjectionFactor(std::size_t level, std::size_t id) const {
			for(auto it = polys(level)[id]->second.begin(); it != polys(level)[id]->second.end(); it++) {
				if(hasPolynomialById(it->level, it->first) &&  hasPolynomialById(it->level, it->second)) {
					return true;
				}
			}
			return false;
		}
		void removeProjectionFactor(std::size_t level, std::size_t id) {
			auto p = polys(level)[id];
			auto it = polyIDs(level).find(p->first);

			polyIDs(level).erase(it);
			polys(level)[id] = boost::none;
			freeID(level, id);

			carl::Bitset removed;
			removed.set(id);
			callRemoveCallback(level, removed);
		}

		std::size_t size(std::size_t level) const override {
			return polys(level).size();
		}
		bool empty(std::size_t level) const override {
			return polyIDs(level).empty();
		}

		bool hasPolynomialById(std::size_t level, std::size_t id) const override {
		 assert(level > 0 && level <= dim());
		 assert(id < polys(level).size());
		 return bool(polys(level)[id]);
		}
		const UPoly& getPolynomialById(std::size_t level, std::size_t id) const override {
			assert(level > 0 && level <= dim());
			assert(id < polys(level).size());
			assert(polys(level)[id]);
			return polys(level)[id]->first;
		}
	};

	template<typename S>
	std::ostream& operator<<(std::ostream& os, const Projection<S>& p) {
	for (std::size_t level = 1; level <= p.dim(); level++) {
		os << level << " " << p.var(level) << ":" << std::endl;
		for (const auto& it: p.polyIDs(level)) {
			assert(p.polys(level)[it.second]);
			os << "\t" << it.second << ": " << p.polys(level)[it.second]->first << " " << p.polys(level)[it.second]->second << std::endl;
		}
	}
	return os;
	}
}
