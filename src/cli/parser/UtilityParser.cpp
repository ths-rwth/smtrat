#include "UtilityParser.h"

#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>

namespace smtrat {
namespace parser {

TheoryOpParser::TheoryOpParser() {
    add("+", Poly::ConstructorOperation::ADD);
    add("-", Poly::ConstructorOperation::SUB);
    add("*", Poly::ConstructorOperation::MUL);
    add("/", Poly::ConstructorOperation::DIV);
}

DomainParser::DomainParser() {
    add("Bool", carl::VariableType::VT_BOOL);
    add("Int", carl::VariableType::VT_INT);
    add("Real", carl::VariableType::VT_REAL);
}

BooleanOpParser::BooleanOpParser() {
    add("and", carl::FormulaType::AND);
    add("or", carl::FormulaType::OR);
    add("xor", carl::FormulaType::XOR);
    add("iff", carl::FormulaType::IFF);
}

LogicParser::LogicParser() {
    add("QF_LIA", smtrat::Logic::QF_LIA);
    add("QF_LRA", smtrat::Logic::QF_LRA);
    add("QF_NIA", smtrat::Logic::QF_NIA);
    add("QF_NRA", smtrat::Logic::QF_NRA);
    add("QF_UF", smtrat::Logic::QF_NRA);
}

RelationParser::RelationParser() {
    add("<=", carl::Relation::LEQ);
    add(">=", carl::Relation::GEQ);
    add("<", carl::Relation::LESS);
    add(">", carl::Relation::GREATER);   
    add("<>", carl::Relation::NEQ);
}

BoundaryParser::BoundaryParser(): BoundaryParser::base_type(main, "bounary") {
	main = &qi::no_skip[(qi::space | qi::char_(")"))];
}

StringParser::StringParser() : StringParser::base_type(main, "string") {
    main = qi::no_skip[qi::char_('"') > +(escapes | ~qi::char_('"')) > qi::char_('"')];
    main.name("string");
    escapes.add("\\\\", '\\');
    escapes.add("\\\"", '"');
    escapes.name("escape sequences");
}

KeywordParser::KeywordParser() : KeywordParser::base_type(main, "keyword") {
    main = qi::lit(":") >> qi::lexeme[ +(qi::alnum | qi::char_("~!@$%^&*_+=<>.?/-"))];
    main.name("keyword");
}

SymbolParser::SymbolParser() : SymbolParser::base_type(main, "symbol") {
    main = quoted | simple;
    main.name("symbol");
    quoted = qi::lit('|') > qi::no_skip[+(~qi::char_("|")) > qi::lit('|')];
    quoted.name("quoted symbol");
    // Attention: "-" must be the first or last character!
    simple = qi::lexeme[ (qi::alpha | qi::char_("~!@$%^&*_+=<>.?/-")) > *(qi::alnum | qi::char_("~!@$%^&*_+=<>.?/-"))];
    simple.name("simple symbol");
}

IdentifierParser::IdentifierParser() : KeywordParser::base_type(main, "identifier") {
    main = symbol | indexed;
    main.name("identifier");
    indexed = (qi::lit("(") >> qi::lit("_") >> symbol >> +numeral >> qi::lit(")"))[qi::_val = px::bind(&IdentifierParser::buildIdentifier, px::ref(*this), qi::_1, qi::_2)];
    indexed.name("indexed symbol");
}

std::string IdentifierParser::buildIdentifier(const std::string& name, const std::vector<Rational>& nums) const {
    assert(nums.size() > 0);
    std::stringstream ss;
    ss << name << "|" << nums.front();
    for (unsigned i = 1; i < nums.size(); i++) ss << "," << nums[i];
    return ss.str();
}

ValueParser::ValueParser(): ValueParser::base_type(main, "value") {
	main = qi::bool_ | symbol | string | decimal | integral;
}

AttributeParser::AttributeParser(): AttributeParser::base_type(main, "attribute") {
	main = (keyword > -value)[qi::_val = px::construct<Attribute>(qi::_1, qi::_2)];
}

}
}