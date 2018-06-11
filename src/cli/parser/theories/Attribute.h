#pragma once

#include "Common.h"
#include "TheoryTypes.h"

namespace smtrat {
namespace parser {
	
/**
 * Represents an Attribute.
 */
class Attribute {
public:
	using AttributeValue = types::AttributeValue;
	std::string key;
	AttributeValue value;

	Attribute() {}
	explicit Attribute(const std::string& key) : key(key) {}
	Attribute(const std::string& key, const AttributeValue& value) : key(key), value(value) {
		simplify();
	}
	Attribute(const std::string& key, const boost::optional<AttributeValue>& value) : key(key) {
		if (value.is_initialized()) this->value = value.get();
		simplify();
	}
	//Attribute(const std::string& key, bool value): key(key), value(FormulaT(value ? carl::FormulaType::TRUE : carl::FormulaType::FALSE)) {}

	bool hasValue() const {
		return boost::get<boost::spirit::unused_type>(&value) == nullptr;
	}
	void simplify() {
		if (FormulaT* f = boost::get<FormulaT>(&value)) {
			if (f->isTrue()) value = true;
			else if (f->isFalse()) value = false;
		}
	}
};
inline std::ostream& operator<<(std::ostream& os, const Attribute& attr) {
	os << "(:" << attr.key;
	if (attr.hasValue()) os << " " << attr.value;
	return os << ")";
}

}
}
