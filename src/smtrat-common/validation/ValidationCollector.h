#pragma once

#include "../carl/util/Singleton.h"

#include <memory>
#include <string>
#include <vector>

namespace smtrat {
namespace validation {

class ValidationPoint;

class ValidationCollector: public carl::Singleton<ValidationCollector> {
private:
	std::vector<std::unique_ptr<ValidationPoint>> mPoints;
public:
	template<typename T>
	T& get(const std::string& name) {
		auto& ptr = mPoints.emplace_back(std::make_unique<T>());
		ptr->set_name(name);
		return static_cast<T&>(*ptr);
	}

	const auto& points() const {
		return mPoints;
	}
};

template<typename T>
auto& get(const std::string& name) {
	return ValidationCollector::getInstance().get<T>(name);
}

}
}