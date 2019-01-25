#pragma once

#include "../config.h"
#include "StatisticsCollector.h"

#include <map>
#include <sstream>

namespace smtrat {

class Statistics {
private:
	std::string mName;
	std::map<std::string, std::string> mCollected;
protected:
	template<typename T>
	void addKeyValuePair(const std::string& key, const T& value) {
		if constexpr(std::is_same<T,std::string>::value) {
			mCollected.emplace(key, value);
		} else {
			std::stringstream ss;
			ss << value;
			mCollected.emplace(key, ss.str());
		}
	}
public:
	explicit Statistics(std::string name): mName(std::move(name)) {
		StatisticsCollector::getInstance().registerStats(this);
	}

	Statistics(const Statistics&) = delete;
	Statistics(Statistics&&) = delete;
	Statistics& operator=(const Statistics&) = delete;
	Statistics& operator=(Statistics&&) = delete;
	virtual ~Statistics() = default;

	virtual bool enabled() const {
		return true;
	}
	virtual void collect() {}

	const auto& name() const {
		return mName;
	}
	const auto& collected() const {
		return mCollected;
	}
};

} // smtrat
