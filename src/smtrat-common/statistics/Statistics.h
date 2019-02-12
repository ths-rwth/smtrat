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
	Statistics() = default;
	virtual ~Statistics() = default;
	Statistics(const Statistics&) = delete;
	Statistics(Statistics&&) = delete;
	Statistics& operator=(const Statistics&) = delete;
	Statistics& operator=(Statistics&&) = delete;

	void set_name(const std::string& name) {
		mName = name;
	}

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
