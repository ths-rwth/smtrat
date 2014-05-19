/**
 * @file ParserUtils.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <algorithm>
#include <sstream>
#include <type_traits>
#include <boost/spirit/include/qi.hpp>

#include "../../lib/Common.h"
#include "Driver.h"

namespace spirit = boost::spirit;
namespace qi = boost::spirit::qi;
namespace px = boost::phoenix;

namespace smtrat {
namespace parser {

struct SuccessHandler {	
	template<typename Parser, typename Rule, typename Entity>
	void operator()(Parser& p, const Rule& rule, const Entity& entity) const {
		p.lastrule.str("");
		p.lastrule << rule.name();
		p.lastentity.str("");
		p.lastentity << entity;
		//std::cout << "rule " << p.lastrule.str() << " : " << p.lastentity.str() << std::endl;
	}
};

struct ErrorHandler {
	template<typename Parser, typename T1, typename T2, typename T3, typename T4>
	qi::error_handler_result operator()(const Parser& p, T1 b, T2 e, T3 where, T4 const& what) const {
		auto line_start = spirit::get_line_start(b, where);
		auto line_end = std::find(where, e, '\n');
		std::string line(++line_start, line_end);
		std::string input(where, line_end);
		
		std::cerr << std::endl;
		std::cerr << "Parsing error at " << spirit::get_line(where) << ":" << spirit::get_column(line_start, where) << std::endl;
		std::cerr << "after parsing rule " << p.lastrule.str() << ": " << p.lastentity.str() << std::endl;
		std::cerr << "expected" << std::endl << "\t" << what.tag << ": " << what << std::endl;
		std::cerr << "but got" << std::endl << "\t" << input << std::endl;
		std::cerr << "in line " << spirit::get_line(where) << std::endl << "\t" << line << std::endl;
		return qi::fail;
	}
};


struct RationalPolicies : qi::ureal_policies<smtrat::Rational> {
	template <typename It, typename Attr>
	static bool parse_nan(It&, It const&, Attr&) { return false; }
	template <typename It, typename Attr>
	static bool parse_inf(It&, It const&, Attr&) { return false; }
};

template<typename Iterator, typename Skipper>
struct SymbolParser : public qi::grammar<Iterator, std::string(), Skipper> {
	SymbolParser() : SymbolParser::base_type(main, "symbol") {
		main = quoted | simple;
		main.name("symbol");
		quoted = "|" > qi::ascii::print > "|";
		quoted.name("quoted symbol");
		// Attention: "-" must be the first or last character!
		simple = qi::as_string[qi::raw[qi::lexeme[ (qi::alpha | qi::char_("~!@$%^&*_+=<>.?/-")) > *(qi::alnum | qi::char_("~!@$%^&*_+=<>.?/-")) ]]];
		simple.name("simple symbol");
	}
	qi::rule<Iterator, std::string(), Skipper> main;
	qi::rule<Iterator, std::string(), Skipper> quoted;
	qi::rule<Iterator, std::string(), Skipper> simple;
};

struct RelationParser : public qi::symbols<char, Relation> {
	RelationParser() {
		add("=", Relation::EQ);
		add("<=", Relation::LEQ);
		add("=>", Relation::GEQ);
		add("<", Relation::LESS);
		add(">", Relation::GREATER);
		add("<>", Relation::NEQ);
	}
};

enum TheoryOperation : unsigned { ADD, SUB, MUL, DIV };
enum BooleanOperation : unsigned { AND, OR, XOR, IFF };

struct TheoryOpParser : public qi::symbols<char, TheoryOperation> {
	TheoryOpParser() {
		add("+", TheoryOperation::ADD);
		add("-", TheoryOperation::SUB);
		add("*", TheoryOperation::MUL);
		add("/", TheoryOperation::DIV);
	}
};

struct BooleanOpParser : public qi::symbols<char, smtrat::Type> {
	BooleanOpParser() {
		add("and", smtrat::AND);
		add("or", smtrat::OR);
		add("xor", smtrat::XOR);
		add("iff", smtrat::IFF);
	}
};

struct LogicParser : public qi::symbols<char, smtrat::Logic> {
	LogicParser() {
		add("QF_LIA", smtrat::Logic::QF_LIA);
		add("QF_LRA", smtrat::Logic::QF_LRA);
		add("QF_NIA", smtrat::Logic::QF_NIA);
		add("QF_NRA", smtrat::Logic::QF_NRA);
	}
};


}
}

namespace boost { namespace spirit { namespace traits { 
	template<> inline void scale(int exp, smtrat::Rational& r) {
		assert(exp >= 0);
		r = carl::pow(r, (unsigned)exp);
	}
	template<> inline bool is_equal_to_one(const smtrat::Rational& value) {
        return value == 1;
    }
}}}