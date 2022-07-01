#pragma once

#include <carl-common/memory/Singleton.h>

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
	ValidationPoint& get(const std::string& channel, const std::string& file, int line) {
		auto& ptr = m_points.emplace_back(std::make_unique<ValidationPoint>());
		ptr->set_identifier(channel, file, line);
		return static_cast<ValidationPoint&>(*ptr);
	}

	const auto& points() const {
		return m_points;
	}
};

inline auto& get(const std::string& channel, const std::string& file, int line) {
	return ValidationCollector::getInstance().get(channel, file, line);
}

}
}