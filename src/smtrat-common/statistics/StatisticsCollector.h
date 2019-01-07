#pragma once

#include <carl/util/Singleton.h>

#include <vector>

namespace smtrat {

class Statistics;

class StatisticsCollector: public carl::Singleton<StatisticsCollector> {
private:
	std::vector<Statistics*> mStats;
public:
	void registerStats(Statistics* s) {
		mStats.emplace_back(s);
	}

	void collect();

	const auto& statistics() const {
		return mStats;
	}
};

}