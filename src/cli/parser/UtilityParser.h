#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>
#include <boost/variant.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>


#include "Common.h"
#include "ParserTypes.h"
#include "NumberParser.h"

namespace smtrat {
namespace parser {

namespace spirit = boost::spirit;
namespace qi = boost::spirit::qi;
namespace px = boost::phoenix;

enum TheoryOperation : unsigned { ADD, SUB, MUL, DIV };
enum BooleanOperation : unsigned { AND, OR, XOR, IFF };

struct TheoryOpParser: public qi::symbols<char, Poly::ConstructorOperation> {
    TheoryOpParser();
};

struct DomainParser: public qi::symbols<char, carl::VariableType> {
    DomainParser();
};

struct BooleanOpParser: public qi::symbols<char, carl::FormulaType> {
    BooleanOpParser();
};

struct LogicParser: public qi::symbols<char, smtrat::Logic> {
    LogicParser();
};

struct RelationParser: public qi::symbols<char, carl::Relation> {
    RelationParser();
};

struct BoundaryParser: public qi::grammar<Iterator, Skipper> {
	BoundaryParser();
	qi::rule<Iterator, Skipper> main;
};

struct StringParser: public qi::grammar<Iterator, std::string(), Skipper> {
    StringParser();
    qi::symbols<char, char> escapes;
    qi::rule<Iterator, std::string(), Skipper> main;
};

struct KeywordParser: public qi::grammar<Iterator, std::string(), Skipper> {
    KeywordParser();
    qi::rule<Iterator, std::string(), Skipper> main;
};

struct SymbolParser: public qi::grammar<Iterator, std::string(), Skipper> {
    SymbolParser();
    qi::rule<Iterator, std::string(), Skipper> main;
    qi::rule<Iterator, std::string(), Skipper> quoted;
    qi::rule<Iterator, std::string(), Skipper> simple;
};

struct IdentifierParser: public qi::grammar<Iterator, std::string(), Skipper> {
    IdentifierParser();
    SymbolParser symbol;
    qi::uint_parser<Rational,10,1,-1> numeral;
    qi::rule<Iterator, std::string(), Skipper> main;
    qi::rule<Iterator, std::string(), Skipper> indexed;
    std::string buildIdentifier(const std::string& name, const std::vector<Rational>& nums) const;
};

template<typename T>
struct DeclaredSymbolParser: public qi::grammar<Iterator, T(), Skipper> {
    DeclaredSymbolParser(): DeclaredSymbolParser::base_type(main, "declared symbol") {
        main = (qi::lit('|') >> sym >> qi::lit('|')) | sym;
        main.name("declared symbol");
    }
    qi::rule<Iterator, T(), Skipper> main;
    qi::symbols<char, T> sym;  
};

struct ValueParser: public qi::grammar<Iterator, AttributeMandatoryValue(), Skipper> {
	ValueParser(): ValueParser::base_type(main, "value") {
		main = qi::bool_ | symbol | string | decimal | integral;
	}
	SymbolParser symbol;
	StringParser string;
	DecimalParser decimal;
	IntegralParser integral;
	qi::rule<Iterator, AttributeMandatoryValue(), Skipper> main;
};

struct AttributeParser: public qi::grammar<Iterator, Attribute(), Skipper> {
	AttributeParser(): AttributeParser::base_type(main, "attribute") {
		main = (keyword > -value)[qi::_val = px::construct<Attribute>(qi::_1, qi::_2)];
	}
	KeywordParser keyword;
	ValueParser value;
	qi::rule<Iterator, Attribute(), Skipper> main;
};

}
}