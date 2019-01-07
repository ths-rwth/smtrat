#pragma once

#include <carl/util/Singleton.h>

#include <vector>

namespace smtrat {

class Statistics2;

class StatisticsCollector: public carl::Singleton<StatisticsCollector> {
private:
	std::vector<Statistics2*> mStats;
public:
	void registerStats(Statistics2* s) {
		mStats.emplace_back(s);
	}

	void collect();

	const auto& statistics() const {
		return mStats;
	}
};

}