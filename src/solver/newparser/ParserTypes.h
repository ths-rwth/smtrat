/**
 * @file Common.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <cxxabi.h>
#include <iostream>
#include <map>
#include <typeinfo>

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/variant.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>

#include "../../lib/Common.h"

namespace smtrat {
namespace parser {
	
namespace spirit = boost::spirit;
namespace qi = boost::spirit::qi;
namespace px = boost::phoenix;

typedef boost::spirit::istream_iterator BaseIteratorType;
typedef boost::spirit::line_pos_iterator<BaseIteratorType> PositionIteratorType;
typedef PositionIteratorType Iterator;
#define SKIPPER (qi::space | qi::lit(";") >> *(qi::char_ - qi::eol) >> qi::eol)
typedef BOOST_TYPEOF(SKIPPER) Skipper;

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
private:
	std::string demangle(const char* t) const {
		int status;
		char* res = abi::__cxa_demangle(t, 0, 0, &status);
		std::string type(res);
		std::free(res);
		return type;
	}
public:
	template<typename T, typename Output>
	void assertType(const Key& key, Output out) const {
		auto it = this->find(key);
		if (it == this->end()) {
			out() << "No value was set for " << key << ".";
		} else if (boost::get<T>(&(it->second)) == nullptr) {
			out() << "The type of " << key << " should be \"" << demangle(typeid(T).name()) << "\" but is \"" << demangle(it->second.type().name()) << "\".";
		}
	}
	
	template<typename T>
	bool has(const Key& key) const {
		auto it = this->find(key);
		if (it == this->end()) return false;
		return boost::get<T>(&(it->second)) != nullptr;
	}
	template<typename T>
	const T& get(const Key& key) const {
		auto it = this->find(key);
		return boost::get<T>(it->second);
	}
};

}
}