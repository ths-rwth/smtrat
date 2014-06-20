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

#include "../../lib/Common.h"

namespace smtrat {
class Formula;

namespace parser {

enum ExpressionType { BOOLEAN, THEORY };

typedef boost::variant<bool, std::string, Rational, unsigned, boost::spirit::qi::unused_type> AttributeValue;
typedef std::pair<std::string, AttributeValue> Attribute;

typedef boost::spirit::istream_iterator BaseIteratorType;
typedef boost::spirit::line_pos_iterator<BaseIteratorType> PositionIteratorType;
typedef PositionIteratorType Iterator;

typedef boost::variant<const Formula*, Polynomial> Argument;
typedef std::vector<Argument> Arguments;

typedef std::tuple<std::string, std::vector<carl::Variable>, const Formula*> BooleanFunction;
typedef std::tuple<std::string, std::vector<carl::Variable>, Polynomial> TheoryFunction;


}
}