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
#include "../../lib/datastructures/VariantMap.h"
#include "Driver.h"
#include "ParserTypes.h"

namespace smtrat {
namespace parser {

enum ExpressionType { BOOLEAN, THEORY };

struct SuccessHandler {
	template<typename> struct result { typedef void type; };
	template<typename Parser, typename Rule, typename Entity, typename Begin, typename End>
	void operator()(Parser& p, const Rule& rule, const Entity& entity, Begin b, End e) const {
		p.lastrule.str("");
		p.lastrule << rule.name();
		p.lastentity.str("");
		p.lastentity << entity;
		auto line_end = std::find(b, e, '\n');
		std::cout << p.lastrule.str() << ": " << p.lastentity.str() << "\n\t" << std::string(b, line_end) << std::endl;
	}
};
struct SuccessHandlerPtr {
	template<typename> struct result { typedef void type; };
	template<typename Parser, typename Rule, typename Entity, typename Begin, typename End>
	void operator()(Parser& p, const Rule& rule, const Entity& entity, Begin b, End e) const {
		p.lastrule.str("");
		p.lastrule << rule.name();
		p.lastentity.str("");
		p.lastentity << *entity;
		auto line_end = std::find(b, e, '\n');
		std::cout << p.lastrule.str() << ": " << p.lastentity.str() << "\n\t" << std::string(b, line_end) << std::endl;
	}
};

struct ErrorHandler {
	template<typename> struct result { typedef qi::error_handler_result type; };
	template<typename Parser, typename T1, typename T2, typename T3, typename T4>
	qi::error_handler_result operator()(const Parser& p, T1 b, T2 e, T3 where, T4 const& what) const {
		auto line_start = spirit::get_line_start(b, where);
		auto line_end = std::find(where, e, '\n');
		std::string line(++line_start, line_end);
		std::string input(where, line_end);
		
		std::cerr << std::endl;
		std::cerr << "Parsing error at " << spirit::get_line(where) << ":" << spirit::get_column(line_start, where) << std::endl;
		if (p.lastrule.str().size() > 0) {
			std::cerr << "after parsing rule " << p.lastrule.str() << ": " << p.lastentity.str() << std::endl;
		}
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

struct SymbolParser : public qi::grammar<Iterator, std::string(), Skipper> {
	SymbolParser();
	qi::rule<Iterator, std::string(), Skipper> main;
	qi::rule<Iterator, std::string(), Skipper> quoted;
	qi::rule<Iterator, std::string(), Skipper> simple;
};

template<typename T>
struct DeclaredSymbolParser : public qi::grammar<Iterator, T(), Skipper> {
	DeclaredSymbolParser(): DeclaredSymbolParser::base_type(main, "declared symbol") {
		main = (qi::lit('|') >> sym >> qi::lit('|')) | sym;
		main.name("declared symbol");
	}
	qi::rule<Iterator, T(), Skipper> main;
	qi::symbols<char, T> sym;
};

struct StringParser : public qi::grammar<Iterator, std::string(), Skipper> {
	StringParser();
	qi::symbols<char, char> escapes;
	qi::rule<Iterator, std::string(), Skipper> main;
};

struct RelationParser : public qi::symbols<char, Relation> {
	RelationParser();
};

enum TheoryOperation : unsigned { ADD, SUB, MUL, DIV };
enum BooleanOperation : unsigned { AND, OR, XOR, IFF };

struct TheoryOpParser : public qi::symbols<char, Polynomial::ConstructorOperation> {
	TheoryOpParser();
};

struct DomainParser : public qi::symbols<char, carl::VariableType> {
	DomainParser();
};

struct BooleanOpParser : public qi::symbols<char, smtrat::Type> {
	BooleanOpParser();
};

struct LogicParser : public qi::symbols<char, smtrat::Logic> {
	LogicParser();
};

struct IntegralParser : public qi::grammar<Iterator, Rational(), Skipper> {
	IntegralParser() : IntegralParser::base_type(integral, "integral") {
		integral = ("#b" > integralBin) | integralDec | ("#x" > integralHex);
		integral.name("integral number");
	}
	qi::rule<Iterator, Rational(), Skipper> integral;
	qi::uint_parser<Rational,2,1,-1> integralBin;
	qi::uint_parser<Rational,10,1,-1> integralDec;
	qi::uint_parser<Rational,16,1,-1> integralHex;
};

struct DecimalParser : qi::real_parser<Rational, RationalPolicies> {};

struct TypeOfTerm : public boost::static_visitor<ExpressionType> {
	ExpressionType operator()(const Formula*) const { return BOOLEAN; }
	ExpressionType operator()(const Polynomial&) const { return THEORY; }
	ExpressionType operator()(const carl::Variable& v) const { return (*this)(v.getType()); }
	ExpressionType operator()(const carl::VariableType& v) const {
		switch (v) {
			case carl::VariableType::VT_BOOL: return BOOLEAN;
			case carl::VariableType::VT_INT:
			case carl::VariableType::VT_REAL: return THEORY;
			default:
				return THEORY;
		}
	}
	template<typename T>
	static ExpressionType get(const T& t) {
		return TypeOfTerm()(t);
	}
	template<typename... T>
	static ExpressionType get(const boost::variant<T...>& var) {
		return boost::apply_visitor(TypeOfTerm(), var);
	}
};

}
}

namespace boost { namespace spirit { namespace traits { 
	template<> inline void scale(int exp, smtrat::Rational& r) {
		if (exp >= 0)
			r *= carl::pow(smtrat::Rational(10), (unsigned)exp);
		else
			r /= carl::pow(smtrat::Rational(10), (unsigned)(-exp));
	}
	template<> inline bool is_equal_to_one(const smtrat::Rational& value) {
        return value == 1;
    }
}}}