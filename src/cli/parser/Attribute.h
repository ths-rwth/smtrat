#pragma once

#include "Common.h"
#include "Lexicon.h"
#include "SExpression.h"
#include "theories/Attribute.h"
#include "theories/TheoryTypes.h"

namespace smtrat {
namespace parser {

struct AttributeValueParser: public qi::grammar<Iterator, types::AttributeValue(), Skipper> {
	typedef conversion::VariantVariantConverter<types::AttributeValue> Converter;
	AttributeValueParser(): AttributeValueParser::base_type(main, "attribute value") {
		main = 
				specconstant[qi::_val = px::bind(&Converter::template convert<types::ConstType>, &converter, qi::_1)]
			|	symbol[qi::_val = qi::_1]
			|	(qi::lit("(") >> *sexpression >> qi::lit(")"))[qi::_val = px::construct<SExpressionSequence<types::ConstType>>(qi::_1)]
		;
	}
	SpecConstantParser specconstant;
	SymbolParser symbol;
	SExpressionParser sexpression;
	Converter converter;
	qi::rule<Iterator, types::AttributeValue(), Skipper> main;
};


struct AttributeParser: public qi::grammar<Iterator, Attribute(), Skipper> {
	AttributeParser(): AttributeParser::base_type(main, "attribute") {
		main = (keyword > -value)[qi::_val = px::construct<Attribute>(qi::_1, qi::_2)];
	}
	KeywordParser keyword;
	AttributeValueParser value;
	qi::rule<Iterator, Attribute(), Skipper> main;
};

}
}
