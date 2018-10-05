#pragma once

#include "../Common.h"
#include "../utils/Origin.h"

#include <optional>
#include <vector>

namespace smtrat::cad {

class PolynomialInformation {
private:
	using Info = std::tuple<Origin>;
	std::vector<std::vector<std::optional<Info>>> mData;

	bool hasInfo(std::size_t level, std::size_t pid) const {
		assert(level < mData.size());
		if (mData[level].size() <= pid) return false;
		return mData[level][pid].has_value();
	}
public:
	void emplace(std::size_t level, std::size_t pid) {
		while (mData.size() <= level) mData.emplace_back();
		while (mData[level].size() <= pid) mData[level].emplace_back();
		mData[level][pid] = Info();
	}
	const auto& origin(std::size_t level, std::size_t pid) const {
		assert(hasInfo(level, pid));
		return std::get<0>(*mData[level][pid]);
	}
	auto& origin(std::size_t level, std::size_t pid) {
		assert(hasInfo(level, pid));
		return std::get<0>(*mData[level][pid]);
	}

	void clear(std::size_t level, std::size_t pid) {
		mData[level][pid] = std::nullopt;
	}
	void clear() {
		mData.clear();
	}
};

}
