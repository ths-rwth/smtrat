#pragma once

#include "../Common.h"
#include "../utils/Origin.h"

#include <optional>
#include <vector>

namespace smtrat::cad {

class ProjectionLevelInformation {
private:
	struct LevelInfo {
		/// Which polynomials are bounds.
		carl::Bitset bounds;
		/// Which polynomials are equational constraints.
		carl::Bitset equational;
		/// Which polynomials have been evaluated w.r.t. purging.
		carl::Bitset evaluated;
		/// Which polynomials are purged from the projection. (usually due to bounds)
		carl::Bitset purged;
		
		bool isBound(std::size_t pid) const {
			return bounds.test(pid);
		}
		void setBound(std::size_t pid, bool isBound) {
			bounds.set(pid, isBound);
		}

		bool isEquational(std::size_t pid) const {
			return equational.test(pid);
		}
		void setEquational(std::size_t pid, bool isEquational) {
			equational.set(pid, isEquational);
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

	struct PolyInfo {
		Origin origin;
	};
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

}
