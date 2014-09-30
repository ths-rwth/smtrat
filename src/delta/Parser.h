/**
 * @file Parser.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <fstream>
#include <tuple>

#define BOOST_SPIRIT_USE_PHOENIX_V3

#include <boost/variant.hpp>
#include <boost/fusion/include/std_pair.hpp>
#include <boost/fusion/adapted/std_tuple.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/qi_numeric.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_statement.hpp>

#include "Node.h"

namespace delta {

typedef boost::spirit::istream_iterator BaseIteratorType;
typedef boost::spirit::line_pos_iterator<BaseIteratorType> PositionIteratorType;
typedef PositionIteratorType Iterator;

namespace spirit = boost::spirit;
namespace qi = boost::spirit::qi;
namespace px = boost::phoenix;

/**
 * This class is a `boost::spirit::qi` grammar that matches whitespaces and smtlib comments.
 */
struct Skipper : public qi::grammar<Iterator> {
	Skipper(): Skipper::base_type(main, "skipper")  {
		main = (qi::space | qi::lit(";") >> *(qi::char_ - qi::eol) >> qi::eol);
	}
	qi::rule<Iterator> main;
};

/**
 * This class is a `boost::spirit::qi` grammar that matches all kinds of smtlib symbols, numbers etc.
 */
struct SymbolParser : public qi::grammar<Iterator, std::string(), Skipper> {
	SymbolParser(): SymbolParser::base_type(main, "symbol") {
		main = quoted | simple;
		main.name("symbol");
		quoted = qi::char_('|') > qi::no_skip[+(~qi::char_("|")) > qi::char_('|')];
		quoted.name("quoted symbol");
		// Attention: "-" must be the first or last character!
		simple = qi::lexeme[ (qi::alnum | qi::char_("~\":!@$%^&*_+=<>.?/-")) > *(qi::alnum | qi::char_("~\":!@$%^&*_+=<>.?/-"))];
		simple.name("simple symbol");
	}
	qi::rule<Iterator, std::string(), Skipper> main;
	qi::rule<Iterator, std::string(), Skipper> quoted;
	qi::rule<Iterator, std::string(), Skipper> simple;
};

/**
 * This class parses a whole smtlib file into a hierarchy of Node objects.
 */
class Parser {
	/// Parses symbols.
	SymbolParser symbol;
	/// Parses a Node that consists of a symbol.
	qi::rule<Iterator, std::tuple<std::string, bool>(), Skipper> symbol_node;
	/// Parses a Node that is empty.
	qi::rule<Iterator, std::tuple<std::vector<Node>, bool>(), Skipper> empty_node;
	/// Parses a Node that consists of a symbol and further children.
	qi::rule<Iterator, std::tuple<std::string, std::vector<Node>, bool>(), Skipper> full_node;
	/// Parses any Node.
	qi::rule<Iterator, Node(), Skipper> node;
	/// Parses a smtlib file.
	qi::rule<Iterator, std::vector<Node>(), Skipper> main;
	
public:
	/**
	 * Constructs the parsing rules.
	 */
	Parser() {
		symbol_node.name("symbol node");
		symbol_node = symbol >> qi::attr(false);
		full_node = qi::lit("(") >> symbol >> *node >> qi::attr(true) >> qi::lit(")");
		full_node.name("full node");
		empty_node = qi::lit("(") >> *node >> qi::attr(true) >> qi::lit(")");
		empty_node.name("empty node");
		node = symbol_node | full_node | empty_node;
		node.name("node");
		main = *node >> qi::eoi;
		main.name("main");
	}

	/**
	 * Parses a file into a node.
	 * @param filename Filename of the input file.
	 * @return Node object produced by the parser.
	 */
	Node parseFile(const std::string& filename) {
		std::ifstream in(filename);
		in.unsetf(std::ios::skipws);
		BaseIteratorType basebegin(in);
		Iterator begin(basebegin);
		Iterator end;
		Skipper skipper;
		std::vector<Node> n;
		auto res = qi::phrase_parse(begin, end, main, skipper, n);
		if (!res) {
			std::cerr << "Parser error." << std::endl;
		}
		return Node(n, false);
	}
	
	/**
	 * Parses a file into a node.
	 * @param filename Filename of the input file.
	 * @return Node object produced by the parser.
	 */
	static Node parse(const std::string& filename) {
		Parser p;
		return p.parseFile(filename);
	}
};

}
