#pragma once

#include "Common.h"
#include "Lexicon.h"
#include "SExpression.h"

namespace smtrat {
namespace parser {

typedef boost::variant<bool, std::string, carl::Variable, Integer, Rational, Poly, FormulaT, SExpressionSequence, boost::spirit::qi::unused_type> AttributeValue;
typedef boost::variant<bool, std::string, carl::Variable, Integer, Rational, Poly, FormulaT, SExpressionSequence> AttributeMandatoryValue;

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
	//if (attr.hasValue()) os << " " << attr.value;
	return os;
}

struct AttributeValueParser: public qi::grammar<Iterator, AttributeMandatoryValue(), Skipper> {
	typedef VariantConverter<AttributeMandatoryValue> Converter;
	AttributeValueParser(): AttributeValueParser::base_type(main, "attribute value") {
		main = 
				specconstant[qi::_val = px::bind(&Converter::template convert<Theories::ConstType>, &converter, qi::_1)]
			|	symbol[qi::_val = px::bind(&Converter::template convert<std::string>, px::ref(converter), qi::_1)]
			|	(qi::lit("(") >> *sexpression >> qi::lit(")"))[qi::_val = px::bind(&Converter::template convert<SExpressionSequence>, px::ref(converter), px::construct<SExpressionSequence>(qi::_1))]
		;
	}
	SpecConstantParser specconstant;
	SymbolParser symbol;
	SExpressionParser sexpression;
	Converter converter;
	qi::rule<Iterator, AttributeMandatoryValue(), Skipper> main;
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
