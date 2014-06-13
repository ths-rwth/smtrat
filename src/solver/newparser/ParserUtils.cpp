#include "ParserUtils.h"

#include "Common.h"

namespace smtrat {
namespace parser {

SymbolParser::SymbolParser() : SymbolParser::base_type(main, "symbol") {
	main = quoted | simple;
	main.name("symbol");
	quoted = qi::lit('|') > qi::no_skip[+(~qi::char_("|")) > qi::lit('|')];
	quoted.name("quoted symbol");
	// Attention: "-" must be the first or last character!
	simple = qi::as_string[qi::raw[qi::lexeme[ (qi::alpha | qi::char_("~!@$%^&*_+=<>.?/-")) > *(qi::alnum | qi::char_("~!@$%^&*_+=<>.?/-"))]]];
	simple.name("simple symbol");
}

StringParser::StringParser() : StringParser::base_type(main, "string") {
	main = qi::no_skip[qi::char_('"') > +(escapes | ~qi::char_('"')) > qi::char_('"')];
	main.name("string");
	escapes.add("\\\\", '\\');
	escapes.add("\\\"", '"');
	escapes.name("escape sequences");
}

RelationParser::RelationParser() {
	add("=", Relation::EQ);
	add("<=", Relation::LEQ);
	add(">=", Relation::GEQ);
	add("<", Relation::LESS);
	add(">", Relation::GREATER);
	add("<>", Relation::NEQ);
}

TheoryOpParser::TheoryOpParser() {
	add("+", Polynomial::ConstructorOperation::ADD);
	add("-", Polynomial::ConstructorOperation::SUB);
	add("*", Polynomial::ConstructorOperation::MUL);
	add("/", Polynomial::ConstructorOperation::DIV);
}

DomainParser::DomainParser() {
	add("Bool", carl::VariableType::VT_BOOL);
	add("Int", carl::VariableType::VT_INT);
	add("Real", carl::VariableType::VT_REAL);
}

BooleanOpParser::BooleanOpParser() {
	add("and", smtrat::AND);
	add("or", smtrat::OR);
	add("xor", smtrat::XOR);
	add("iff", smtrat::IFF);
	add("=", smtrat::IFF);
}

LogicParser::LogicParser() {
	add("QF_LIA", smtrat::Logic::QF_LIA);
	add("QF_LRA", smtrat::Logic::QF_LRA);
	add("QF_NIA", smtrat::Logic::QF_NIA);
	add("QF_NRA", smtrat::Logic::QF_NRA);
}

}
}