/**
 * @file Common.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#include "theories/Common.h"

#include <algorithm>
#include <functional>
#include <iostream>
#include <sstream>

#include <boost/fusion/include/std_pair.hpp>
#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/qi_parse.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_statement.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>

#include <carl-model/Assignment.h>


#define PARSER_BITVECTOR

#define EXIT_ON_ERROR
#ifdef EXIT_ON_ERROR
#define HANDLE_ERROR std::cout << "(unknown)" << std::endl; exit(123);
#else
#define HANDLE_ERROR
#endif

namespace smtrat {
namespace parser {

	namespace spirit = boost::spirit;
	namespace qi = boost::spirit::qi;
	namespace px = boost::phoenix;

	typedef boost::spirit::istream_iterator BaseIteratorType;
	typedef boost::spirit::line_pos_iterator<BaseIteratorType> PositionIteratorType;
	typedef PositionIteratorType Iterator;

	struct Skipper: public boost::spirit::qi::grammar<Iterator> {
		Skipper(): Skipper::base_type(main, "skipper") {
			main = (boost::spirit::qi::space | boost::spirit::qi::lit(";") >> *(boost::spirit::qi::char_ - boost::spirit::qi::eol) >> boost::spirit::qi::eol);
		};
	    boost::spirit::qi::rule<Iterator> main;
	};

}
}
