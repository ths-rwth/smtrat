#pragma once

#include "Common.h"
#include "Lexicon.h"

#include "theories/Theories.h"

namespace smtrat {
namespace parser {
	
struct SpecConstantParser: public qi::grammar<Iterator, types::ConstType(), Skipper> {
	SpecConstantParser(): SpecConstantParser::base_type(main, "spec_constant") {
		Theories::addConstants(theoryConst);
        main = decimal | numeral | hexadecimal | binary | string | theoryConst;
    }
	NumeralParser numeral;
	DecimalParser decimal;
	HexadecimalParser hexadecimal;
	BinaryParser binary;
	StringParser string;
	
	qi::symbols<char, types::ConstType> theoryConst;
	
    qi::rule<Iterator, types::ConstType(), Skipper> main;
};

struct SExpressionParser: public qi::grammar<Iterator, SExpression<types::ConstType>(), Skipper> {
	typedef conversion::VariantVariantConverter<SExpression<types::ConstType>> Converter;
	SExpressionParser(): SExpressionParser::base_type(main, "sexpression") {
		main = 
				specconstant[qi::_val = px::bind(&Converter::template convert<types::ConstType>, &converter, qi::_1)]
			|	symbol[qi::_val = px::bind(&Converter::template convert<std::string>, px::ref(converter), qi::_1)]
			|	keyword[qi::_val = px::bind(&Converter::template convert<std::string>, px::ref(converter), qi::_1)]
			|	(qi::lit("(") >> *main >> qi::lit(")"))[qi::_val = px::bind(&Converter::template convert<SExpressionSequence<types::ConstType>>, px::ref(converter), px::construct<SExpressionSequence<types::ConstType>>(qi::_1))]
		;
	}
	SpecConstantParser specconstant;
	SymbolParser symbol;
	KeywordParser keyword;
	Converter converter;
	qi::rule<Iterator, SExpression<types::ConstType>(), Skipper> main;
};

}
}
