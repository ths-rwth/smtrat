#pragma once

#include <carl/util/Singleton.h>

#include "ValidationPoint.h"

#include <memory>
#include <string>
#include <vector>

namespace smtrat {
namespace validation {

class ValidationCollector: public carl::Singleton<ValidationCollector> {
private:
	std::vector<std::unique_ptr<ValidationPoint>> m_points;
public:
	ValidationPoint& get(const std::string& channel, const std::string& name) {
		auto& ptr = m_points.emplace_back(std::make_unique<ValidationPoint>());
		ptr->set_identifier(channel, name);
		return static_cast<ValidationPoint&>(*ptr);
	}

	const auto& points() const {
		return m_points;
	}
};

inline auto& get(const std::string& channel, const std::string& name) {
	return ValidationCollector::getInstance().get(channel, name);
}

}
}