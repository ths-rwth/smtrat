#pragma once

#include <smtrat-common/statistics/Statistics.h>

namespace smtrat::analyzer {

struct AnalyzerStatistics: public Statistics {
public:
	template<typename T>
	void add(const std::string& key, const T& value) {
		addKeyValuePair(key, value);
	}
};

}