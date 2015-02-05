/**
 * @file Common.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <iostream>
#include <map>
#include <typeinfo>

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/variant.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>

#include "Common.h"

namespace smtrat {

namespace parser {

enum class ExpressionType : unsigned { BOOLEAN, THEORY, UNINTERPRETED, BITVECTOR };

struct Identifier {
	std::string symbol;
	std::vector<std::size_t>* indices;
	Identifier(): symbol(""), indices(nullptr) {}
	Identifier(const std::string& symbol): symbol(symbol), indices(nullptr) {}
	Identifier(const std::string& symbol, const std::vector<std::size_t>& indices): symbol(symbol), indices(new std::vector<std::size_t>(indices)) {}
	Identifier& operator=(const Identifier& i) {
		symbol = i.symbol;
		delete indices;
		indices = nullptr;
		if (i.indices != nullptr) indices = new std::vector<std::size_t>(*i.indices);
		return *this;
	}
	~Identifier() {
		delete indices;
	}
	operator std::string() const {
		if (indices == nullptr || indices->size() == 0) {
			return symbol;
		}
		std::stringstream ss;
		ss << symbol << "|" << indices->front();
		for (std::size_t i = 1; i < indices->size(); i++) ss << "," << (*indices)[i];
		return ss.str();
	}
};

typedef boost::variant<bool, std::string, Rational, boost::spirit::qi::unused_type> AttributeValue;
typedef boost::variant<bool, std::string, Rational> AttributeMandatoryValue;
class Attribute {
public:
	std::string key;
	AttributeValue value;

	Attribute() {}
	explicit Attribute(const std::string& key) : key(key) {}
	Attribute(const std::string& key, const AttributeMandatoryValue& value) : key(key), value(value) {}
	Attribute(const std::string& key, const boost::optional<AttributeMandatoryValue>& value) : key(key) {
		if (value.is_initialized()) this->value = value.get();
	}

	bool hasValue() const {
		return boost::get<boost::spirit::qi::unused_type>(&value) == nullptr;
	}
};
inline std::ostream& operator<<(std::ostream& os, const Attribute& attr) {
	os << attr.key;
	if (attr.hasValue()) os << " " << attr.value;
	return os;
}

typedef boost::spirit::istream_iterator BaseIteratorType;
typedef boost::spirit::line_pos_iterator<BaseIteratorType> PositionIteratorType;
typedef PositionIteratorType Iterator;


typedef boost::variant<carl::UVariable, carl::UFInstance> UninterpretedType;
typedef boost::variant<FormulaT, Poly, carl::UVariable, carl::UFInstance> Argument;
typedef std::vector<Argument> Arguments;

typedef std::tuple<std::string, std::vector<carl::Variable>, FormulaT> BooleanFunction;
typedef std::tuple<std::string, std::vector<carl::Variable>, Poly> TheoryFunction;



struct Skipper: public boost::spirit::qi::grammar<Iterator> {
	Skipper(): Skipper::base_type(main, "skipper") {
		main = (boost::spirit::qi::space | boost::spirit::qi::lit(";") >> *(boost::spirit::qi::char_ - boost::spirit::qi::eol) >> boost::spirit::qi::eol);
	};
    boost::spirit::qi::rule<Iterator> main;
};

}
}