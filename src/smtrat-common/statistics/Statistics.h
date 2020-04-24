#pragma once

#include "../config.h"
#include "StatisticsCollector.h"

#include <map>
#include <sstream>
#include <algorithm>
#include <assert.h>

namespace smtrat {

class Statistics {
private:
	std::string mName;
	std::map<std::string, std::string> mCollected;
protected:
	template<typename T>
	void addKeyValuePair(const std::string& key, const T& value) {
		assert(std::find_if(key.begin(), key.end(), isspace) == key.end() && "spaces are not allowed here");
		if constexpr(std::is_same<T,std::string>::value) {
			assert(std::find_if(value.begin(), value.end(), isspace) == value.end() && "spaces are not allowed here");
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
