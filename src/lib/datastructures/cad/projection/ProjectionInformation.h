#pragma once

#include "../Common.h"
#include "../utils/Origin.h"

#include <optional>
#include <vector>

namespace smtrat::cad {

class ProjectionGlobalInformation {
public:
	struct ECData {
		std::size_t level = 0;
		carl::Bitset polynomials;
	};
	using ECMap = std::map<Origin::BaseType, ECData>;

	ECMap mECs;
	std::vector<ECMap::const_iterator> mUsedEC;
	// Inactive polynomials in level 0
	carl::Bitset mInactive;

	void reset(std::size_t dim) {
		mECs.clear();
		mUsedEC.assign(dim, mECs.end());
	}

	void createEC(const Origin::BaseType& origin) {
		assert(mECs.find(origin) == mECs.end());
		mECs.emplace(origin, ECData());
	}

	bool isEC(const Origin::BaseType& origin) const {
		return mECs.find(origin) != mECs.end();
	}

	void addToEC(const Origin::BaseType& origin, std::size_t level, std::size_t pid) {
		auto it = mECs.find(origin);
		if (it == mECs.end()) return;
		if (it->second.level == 0 || it->second.level == level) {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Adding " << level << "/" << pid << " to EC " << origin);
			it->second.polynomials.set(pid);
		} else {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "EC " << origin << " is primitive due to " << level << "/" << pid);
		}
	}

	void removeEC(const Origin::BaseType& origin) {
		mECs.erase(origin);
	}
};

class ProjectionLevelInformation {
private:
	struct EquationalConstraint {
		/// Which polynomials belong to this specific equational constraint.
		carl::Bitset polynomials;
		/// Whether this equational constraint can be used.
		/// An equational can not be used, if some factor is primitive.
		bool suitable = true;
	};

	struct EquationalConstraints {
	private:
		/// A list of all ECs in this level, identified by their origin.
		std::vector<EquationalConstraint> mData;
	public:
		/// Add a poly to the respective origin.
		std::size_t addEC() {
			mData.emplace_back();
			return mData.size() - 1;
		}

		void addPolyToEC(std::size_t id, std::size_t pid) {
			mData[id].polynomials.set(pid);
		}

		bool hasEC() const {
			return !mData.empty();
		}
		std::size_t count() const {
			return mData.size();
		}
		const auto& getEC(std::size_t ecid) const {
			return mData[ecid];
		}
		auto& getEC(std::size_t ecid) {
			return mData[ecid];
		}
	};
public:
	struct LevelInfo {
		/// Which polynomials are bounds.
		carl::Bitset bounds;
		/// Which polynomials have been evaluated w.r.t. purging.
		carl::Bitset evaluated;
		/// Which polynomials are purged from the projection. (usually due to bounds)
		carl::Bitset purged;

		/// Equational constraints.
		EquationalConstraints ecs;
		
		bool isBound(std::size_t pid) const {
			return bounds.test(pid);
		}
		void setBound(std::size_t pid, bool isBound) {
			bounds.set(pid, isBound);
		}

		bool isEvaluated(std::size_t pid) const {
			return evaluated.test(pid);
		}
		void setEvaluated(std::size_t pid, bool isEvaluated) {
			evaluated.set(pid, isEvaluated);
		}

		bool isPurged(std::size_t pid) const {
			return purged.test(pid);
		}
		void setPurged(std::size_t pid, bool isPurged) {
			purged.set(pid, isPurged);
		}

		void removePurgedFromEvaluated() {
			evaluated -= purged;
		}
		void restrictEvaluatedToPurged() {
			evaluated &= purged;
		}
	};
private:
	std::vector<LevelInfo> mLevelData;

public:
	bool hasInfo(std::size_t level) const {
		return level < mLevelData.size();
	}

	void emplace(std::size_t level) {
		while (mLevelData.size() <= level) mLevelData.emplace_back();
	}
	const auto& operator()(std::size_t level) const {
		assert(hasInfo(level));
		return mLevelData[level];
	}
	auto& operator()(std::size_t level) {
		assert(hasInfo(level));
		return mLevelData[level];
	}

	void reset(std::size_t dim) {
		mLevelData.clear();
		emplace(dim);
	}
};

class ProjectionPolynomialInformation {
public:
	struct PolyInfo {
		/// Origins of this polynomial.
		Origin origin;
	};
private:
	std::vector<std::vector<std::optional<PolyInfo>>> mPolyData;

public:
	bool hasInfo(std::size_t level, std::size_t pid) const {
		assert(level < mPolyData.size());
		if (mPolyData[level].size() <= pid) return false;
		return mPolyData[level][pid].has_value();
	}
	void emplace(std::size_t level, std::size_t pid) {
		while (mPolyData.size() <= level) mPolyData.emplace_back();
		while (mPolyData[level].size() <= pid) mPolyData[level].emplace_back();
		mPolyData[level][pid] = PolyInfo();
	}
	const auto& operator()(std::size_t level, std::size_t pid) const {
		assert(hasInfo(level, pid));
		return *mPolyData[level][pid];
	}
	auto& operator()(std::size_t level, std::size_t pid) {
		assert(hasInfo(level, pid));
		return *mPolyData[level][pid];
	}
	void clear(std::size_t level, std::size_t pid) {
		mPolyData[level][pid] = std::nullopt;
	}
	void reset(std::size_t dim) {
		mPolyData.clear();
	}
};

class ProjectionInformation {
private:
	ProjectionGlobalInformation mGlobal;
	ProjectionLevelInformation mLevel;
	ProjectionPolynomialInformation mPoly;
public:
	const auto& operator()() const {
		return mGlobal;
	}
	auto& operator()() {
		return mGlobal;
	}

	const auto& operator()(std::size_t level) const {
		return mLevel(level);
	}
	auto& operator()(std::size_t level) {
		return mLevel(level);
	}
	bool hasInfo(std::size_t level) const {
		return mLevel.hasInfo(level);
	}

	const auto& operator()(std::size_t level, std::size_t pid) const {
		return mPoly(level, pid);
	}
	auto& operator()(std::size_t level, std::size_t pid) {
		return mPoly(level, pid);
	}
	void clear(std::size_t level, std::size_t pid) {
		mPoly.clear(level, pid);
	}
	void emplace(std::size_t level, std::size_t pid) {
		mPoly.emplace(level, pid);
	}
	bool hasInfo(std::size_t level, std::size_t pid) const {
		return mPoly.hasInfo(level, pid);
	}

	bool active(std::size_t level, std::size_t id) const {
		if ((*this)(level).isBound(id)) return true;
		if (level == 0) {
			return !mGlobal.mInactive.test(id) && !(*this)(0).isPurged(id);
		} else {
			return (*this)(level, id).origin.isActive() && !(*this)(level).isPurged(id);
		}
	}

	void reset(std::size_t dim) {
		mGlobal.reset(dim);
		mLevel.reset(dim);
		mPoly.reset(dim);
	}

	void addECConstraint(std::size_t pid) {
		SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Add EC " << pid);
		std::size_t ecid = (*this)(0).ecs.addEC();
		(*this)(0).ecs.addPolyToEC(ecid, pid);
	}

	void removeECConstraint(std::size_t pid) {

	}

	bool hasEC(std::size_t level) const {
		return (*this)(level).ecs.hasEC();
	}
	bool usingEC(std::size_t level) const {
		return (*this)().mUsedEC[level] != (*this)().mECs.end();
	}
	const carl::Bitset& getUsedEC(std::size_t level) const {
		assert(hasEC(level));
		assert((*this)().mUsedEC[level]->second.level == level);
		return (*this)().mUsedEC[level]->second.polynomials;
	}
	bool selectEC(std::size_t level) {
		assert(hasEC(level));
		assert(!usingEC(level));
		for (std::size_t ecid = 0; ecid < (*this)(level).ecs.count(); ++ecid) {
			if (!(*this)(level).ecs.getEC(ecid).suitable) continue;
			const auto& polys = (*this)(level).ecs.getEC(ecid).polynomials;
			bool ec_active = true;
			for (auto pid: polys) {
				if (!active(level, pid)) {
					ec_active = false;
					break;
				}
			}
			if (!ec_active) continue;
			
			const auto& ecs = (*this)().mECs;
			for (auto it = ecs.begin(); it != ecs.end(); ++it) {
				//if (it->second == std::make_pair(level, ecid)) {
					(*this)().mUsedEC[level] = it;
					return true;
				//}
			}
		}
		return false;
	}
	void unselectEC(std::size_t level) {
		(*this)().mUsedEC[level] = (*this)().mECs.end();
	}
};

inline std::ostream& operator<<(std::ostream& os, const ProjectionGlobalInformation& gi) {
	for (const auto& ec: gi.mECs) {
		os << "\t" << ec.first << " -> " << ec.second.level << "/" << ec.second.polynomials << std::endl;
	}
	return os;
}
inline std::ostream& operator<<(std::ostream& os, const ProjectionLevelInformation::LevelInfo& li) {
	os << "bounds " << li.bounds << ", purged: " << li.purged << " / " << li.evaluated;
	return os;
}
inline std::ostream& operator<<(std::ostream& os, const ProjectionPolynomialInformation::PolyInfo& pi) {
	os << "origin: " << pi.origin;
	return os;
}

}
