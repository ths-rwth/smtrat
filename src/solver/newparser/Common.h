/**
 * @file Common.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <map>

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/variant.hpp>
#include <boost/spirit/include/qi.hpp>

#include "../../lib/Common.h"

namespace smtrat {
namespace parser {

typedef boost::variant<bool, std::string, Rational, unsigned, boost::spirit::qi::unused_type> Value;
inline std::ostream& operator<<(std::ostream& os, const Value& value) {
	if (value.which() == 0) {
		return os << std::boolalpha << boost::get<bool>(value);
	} else {
		return boost::operator<<(os, value);
	}
}
typedef std::pair<std::string, Value> Attribute;

template<typename Key, typename Value>
class VariantMap : public std::map<Key, Value> {
public:
	template<typename T>
	bool has(const Key& key) {
		auto it = this->find(key);
		if (it == this->end()) return false;
		return boost::get<T>(&(it->second)) != nullptr;
	}
	template<typename T>
	T& get(const Key& key) {
		auto it = this->find(key);
		return boost::get<T>(it->second);
	}
};

}
}