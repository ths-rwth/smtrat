#pragma once

#include "StatisticsCollector.h"

#include <map>
#include <sstream>

namespace smtrat {

class Statistics2 {
private:
	std::string mName;
	std::map<std::string, std::string> mCollected;
protected:
	template<typename T>
	void add(const std::string& key, const T& value) {
		if constexpr(std::is_same<T,std::string>::value) {
			mCollected.emplace(key, value);
		} else {
			std::stringstream ss;
			ss << value;
			mCollected.emplace(key, ss.str());
		}
	}
public:
	Statistics2(std::string name): mName(std::move(name)) {
		StatisticsCollector::getInstance().registerStats(this);
	}

	Statistics2(const Statistics2&) = delete;
	virtual ~Statistics2() = default;

	virtual void collect() {}

	const auto& name() const {
		return mName;
	}
	const auto& collected() const {
		return mCollected;
	}
};

} // smtrat
