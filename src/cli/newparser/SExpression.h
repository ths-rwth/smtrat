#pragma once

#include "Common.h"
#include "Lexicon.h"

#include "theories/Theories.h"

namespace smtrat {
namespace parser {
	
struct SpecConstantParser: public qi::grammar<Iterator, Theories::ConstType(), Skipper> {
	SpecConstantParser(): SpecConstantParser::base_type(main, "spec_constant") {
		Theories::addConstants(theoryConst);
        main = decimal | numeral | hexadecimal | binary | string | theoryConst;
    }
	NumeralParser numeral;
	DecimalParser decimal;
	HexadecimalParser hexadecimal;
	BinaryParser binary;
	StringParser string;
	
	qi::symbols<char, Theories::ConstType> theoryConst;
	
    qi::rule<Iterator, Theories::ConstType(), Skipper> main;
};

struct SExpressionSequence;
typedef boost::variant<Theories::ConstType, boost::recursive_wrapper<SExpressionSequence>> SExpression;
struct SExpressionSequence: public std::vector<SExpression> {
	SExpressionSequence(const std::vector<SExpression>& v): std::vector<SExpression>(v) {}
	SExpressionSequence(std::vector<SExpression>&& v): std::vector<SExpression>(std::move(v)) {}
};
inline std::ostream& operator<<(std::ostream& os, const SExpressionSequence& ses) {
	return os << std::vector<SExpression>(ses);
}

struct SExpressionParser: public qi::grammar<Iterator, SExpression(), Skipper> {
	typedef VariantConverter<SExpression> Converter;
	SExpressionParser(): SExpressionParser::base_type(main, "sexpression") {
		main = 
				specconstant[qi::_val = px::bind(&Converter::template convert<Theories::ConstType>, &converter, qi::_1)]
			|	symbol[qi::_val = px::bind(&Converter::template convert<std::string>, px::ref(converter), qi::_1)]
			|	keyword[qi::_val = px::bind(&Converter::template convert<std::string>, px::ref(converter), qi::_1)]
			|	(qi::lit("(") >> *main >> qi::lit(")"))[qi::_val = px::bind(&Converter::template convert<SExpressionSequence>, px::ref(converter), px::construct<SExpressionSequence>(qi::_1))]
		;
	}
	SpecConstantParser specconstant;
	SymbolParser symbol;
	KeywordParser keyword;
	Converter converter;
	qi::rule<Iterator, SExpression(), Skipper> main;
};

}
}
