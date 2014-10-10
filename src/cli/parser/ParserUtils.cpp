#include "ParserUtils.h"

#include "ParserTypes.h"

namespace smtrat {
namespace parser {

bool checkArguments(const std::string& name, const std::vector<carl::Variable>& types, const Arguments& args, std::map<carl::Variable, const Formula*>& boolAssignments, std::map<carl::Variable, Polynomial>& theoryAssignments, std::function<OutputWrapper()> out) {
	if (types.size() != args.size()) {
		out() << "The number of arguments for \"" << name << "\" does not match its declaration.";
		return false;
	}
	for (unsigned id = 0; id < types.size(); id++) {
		ExpressionType type = TypeOfTerm::get(types[id]);
		if (type != TypeOfTerm::get(args[id])) {
			out() << "The type of argument " << (id+1) << " for \"" << name << "\" did not match the declaration.";
			return false;
		}
		if (type == ExpressionType::BOOLEAN) {
			boolAssignments[types[id]] = boost::get<const Formula*>(args[id]);
		} else {
			theoryAssignments[types[id]] = boost::get<Polynomial>(args[id]);
		}
	}
	return true;
}

const smtrat::Formula* applyBooleanFunction(const BooleanFunction& f, const Arguments& args, std::function<OutputWrapper()> out) {
	std::map<carl::Variable, const Formula*> boolAssignments;
	std::map<carl::Variable, Polynomial> theoryAssignments;
	if (!checkArguments(std::get<0>(f), std::get<1>(f), args, boolAssignments, theoryAssignments, out)) {
		return nullptr;
	}
	return std::get<2>(f)->substitute(boolAssignments, theoryAssignments);
}
Polynomial applyTheoryFunction(const TheoryFunction& f, const Arguments& args, std::function<OutputWrapper()> out) {
	std::map<carl::Variable, const Formula*> boolAssignments;
	std::map<carl::Variable, Polynomial> theoryAssignments;
	if (!checkArguments(std::get<0>(f), std::get<1>(f), args, boolAssignments, theoryAssignments, out)) {
		return smtrat::Polynomial();
	}
	return std::get<2>(f).substitute(theoryAssignments);
}

Skipper::Skipper(): Skipper::base_type(main, "skipper") {
	main = (qi::space | qi::lit(";") >> *(qi::char_ - qi::eol) >> qi::eol);
};

SymbolParser::SymbolParser() : SymbolParser::base_type(main, "symbol") {
	main = quoted | simple;
	main.name("symbol");
	quoted = qi::lit('|') > qi::no_skip[+(~qi::char_("|")) > qi::lit('|')];
	quoted.name("quoted symbol");
	// Attention: "-" must be the first or last character!
	simple = qi::lexeme[ (qi::alpha | qi::char_("~!@$%^&*_+=<>.?/-")) > *(qi::alnum | qi::char_("~!@$%^&*_+=<>.?/-"))];
	simple.name("simple symbol");
}

KeywordParser::KeywordParser() : KeywordParser::base_type(main, "keyword") {
	main = qi::lit(":") >> qi::lexeme[ +(qi::alnum | qi::char_("~!@$%^&*_+=<>.?/-"))];
	main.name("keyword");
}

IdentifierParser::IdentifierParser() : KeywordParser::base_type(main, "identifier") {
	main = symbol | indexed;
	main.name("identifier");
	// should return <symbol>|n,...,n
	//indexed = qi::lit("(") >> qi::lit("_") >> symbol >> qi::attr("|") >> numeral >> *(qi::attr(",") >> numeral) >> qi::lit(")");
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
	add("QF_UF", smtrat::Logic::QF_NRA);
}

}
}