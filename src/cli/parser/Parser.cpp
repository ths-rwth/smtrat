#include "Parser.h"

#include <cassert>
#include <iostream>
#include <limits>
#include <set>

#include "carl/util/debug.h"

namespace smtrat {
namespace parser {

SMTLIBParser::SMTLIBParser(InstructionHandler* ih, bool queueInstructions, bool debug):
	state(new ParserState(ih)),
	handler(ih),
	queueInstructions(queueInstructions),
	formula(state),
	uninterpreted(state, &formula),
	polynomial(state, &formula, &uninterpreted),
	fun_argument(&formula, &uninterpreted, &polynomial)
{
	var = state->var_bool | state->var_theory;
	var.name("variable");

	sortedVar = "(" >> symbol >> sort >> ")";
	sortedVar.name("sorted variable");
	
	fun_definition = symbol[px::bind(&ParserState::pushScope, px::ref(state)), qi::_a = qi::_1] > "(" > 
		*(sortedVar[px::push_back(qi::_b, px::bind(&SMTLIBParser::addVariableBinding, px::ref(*this), qi::_1))]) 
		> ")" > (sort > fun_argument)[px::bind(&SMTLIBParser::defineFun, px::ref(*this), qi::_a, qi::_b, qi::_1, qi::_2)];
	fun_definition.name("function definition");
	
	fun_arguments = *fun_argument;
	fun_arguments.name("function arguments");
	
	cmd = "(" > (
			(qi::lit("assert") > formula > ")")[px::bind(&SMTLIBParser::add, px::ref(*this), qi::_1)]
		|	(qi::lit("check-sat") > ")")[px::bind(&SMTLIBParser::check, px::ref(*this))]
		|	(qi::lit("declare-const") > symbol > sort > ")")[px::bind(&SMTLIBParser::declareConst, px::ref(*this), qi::_1, qi::_2)]
		|	(qi::lit("declare-fun") > symbol > "(" > *sort > ")" > sort > ")")[px::bind(&SMTLIBParser::declareFun, px::ref(*this), qi::_1, qi::_2, qi::_3)]
		|	(qi::lit("declare-sort") > symbol > numeral > ")")[px::bind(&SMTLIBParser::declareSort, px::ref(*this), qi::_1, qi::_2)]
		|	(qi::lit("define-fun") > fun_definition > ")")
		|	(qi::lit("define-sort") > symbol > "(" > (*symbol)[px::bind(&SMTLIBParser::setSortParameters, px::ref(*this), qi::_1)] > ")" > sort > ")")[px::bind(&SMTLIBParser::defineSort, px::ref(*this), qi::_1, qi::_2, qi::_3)]
		|	(qi::lit("exit") > ")")[px::bind(&SMTLIBParser::exit, px::ref(*this))]
		|	(qi::lit("get-assertions") > ")")[px::bind(&SMTLIBParser::getAssertions, px::ref(*this))]
		|	(qi::lit("get-assignment") > ")")[px::bind(&SMTLIBParser::getAssignment, px::ref(*this))]
		|	(qi::lit("get-info") > keyword > ")")[px::bind(&SMTLIBParser::getInfo, px::ref(*this), qi::_1)]
		|	(qi::lit("get-model") > ")")[px::bind(&SMTLIBParser::getAssignment, px::ref(*this))]
		|	(qi::lit("get-option") > keyword > ")")[px::bind(&SMTLIBParser::getOption, px::ref(*this), qi::_1)]
		|	(qi::lit("get-proof") > ")")[px::bind(&SMTLIBParser::getProof, px::ref(*this))]
		|	(qi::lit("get-unsat-core") > ")")[px::bind(&SMTLIBParser::getUnsatCore, px::ref(*this))]
		|	(qi::lit("get-value") > *var > ")")[px::bind(&SMTLIBParser::getValue, px::ref(*this), qi::_1)]
		|	(qi::lit("pop") > (numeral | qi::attr((unsigned)1)) > ")")[px::bind(&SMTLIBParser::pop, px::ref(*this), qi::_1)]
		|	(qi::lit("push") > (numeral | qi::attr((unsigned)1)) > ")")[px::bind(&SMTLIBParser::push, px::ref(*this), qi::_1)]
		|	(qi::lit("set-info") > attribute > ")")[px::bind(&SMTLIBParser::setInfo, px::ref(*this), qi::_1)]
		|	(qi::lit("set-logic") > logic > ")")[px::bind(&SMTLIBParser::setLogic, px::ref(*this), qi::_1)]
		|	(qi::lit("set-option") > attribute > ")")[px::bind(&SMTLIBParser::setOption, px::ref(*this), qi::_1)]
	);
	cmd.name("command");

	main = *cmd > qi::eoi;
	main.name("SMTLib File");

	qi::on_error<qi::fail>(main, errorHandler(px::ref(*this), qi::_1, qi::_2, qi::_3, qi::_4));

	/*if (debug) {
		qi::on_success(bindlist, successHandler(px::ref(*this), px::ref(bindlist), qi::_val, qi::_1, qi::_2));
		qi::on_success(polynomial, successHandler(px::ref(*this), px::ref(polynomial), qi::_val, qi::_1, qi::_2));
		qi::on_success(polynomial_op, successHandler(px::ref(*this), px::ref(polynomial_op), qi::_val, qi::_1, qi::_2));
		qi::on_success(formula, successHandlerPtr(px::ref(*this), px::ref(formula), qi::_val, qi::_1, qi::_2));
		qi::on_success(formula_op, successHandlerPtr(px::ref(*this), px::ref(formula_op), qi::_val, qi::_1, qi::_2));
		qi::on_success(cmd, successHandler(px::ref(*this), px::ref(cmd), qi::_val, qi::_1, qi::_2));
		qi::on_success(main, successHandler(px::ref(*this), px::ref(main), qi::_val, qi::_1, qi::_2));
	}*/
}

bool SMTLIBParser::parse(std::istream& in, const std::string&) {
	in.unsetf(std::ios::skipws);
	mInputStream = &in;
	BaseIteratorType basebegin(in);
	Iterator begin(basebegin);
	Iterator end;
	return qi::phrase_parse(begin, end, main, skipper);
}

void SMTLIBParser::add(FormulaT& f) {
	if (this->handler->printInstruction()) handler->regular() << "(assert " << f << ")" << std::endl;
	//assert(f != nullptr); // @todo Florian, ask Gereon why we must overwrite here.
	if (!state->mTheoryIteBindings.empty()) {
		// There have been theory ite expressions within this formula.
		// We add the formulas from mTheoryIteBindings to the formula.
		state->mTheoryIteBindings.insert(f);
		f = FormulaT(carl::FormulaType::AND, std::move(state->mTheoryIteBindings));
		state->mTheoryIteBindings.clear();
	}
	if (!state->mUninterpretedEqualities.empty()) {
		// There have been uninterpreted expressions within this formula.
		// We add the formulas from mUninterpretedExpressions to the formula.
		state->mUninterpretedEqualities.insert(f);
		f = FormulaT(carl::FormulaType::AND, std::move(state->mUninterpretedEqualities));
		state->mUninterpretedEqualities.clear();
	}
	
	callHandler(&InstructionHandler::add, f);
}
void SMTLIBParser::check() {
	if (this->handler->printInstruction()) handler->regular() << "(check-sat)" << std::endl;
	callHandler(&InstructionHandler::check);
}
void SMTLIBParser::declareConst(const std::string& name, const carl::Sort& sort) {
	if (state->handler->printInstruction()) handler->regular() << "(declare-const " << name << " " << sort << ")" << std::endl;
	assert(state->isSymbolFree(name));
	switch (TypeOfTerm::get(sort)) {
	case ExpressionType::BOOLEAN: {
		if (state->var_bool.sym.find(name) != nullptr) handler->warn() << "a boolean variable with name '" << name << "' has already been defined.";
		carl::Variable var = carl::newBooleanVariable(name, true);
		state->var_bool.sym.add(name, var);
		break;
	}
	case ExpressionType::THEORY: {
		if (state->var_theory.sym.find(name) != nullptr) handler->warn() << "a theory variable with name '" << name << "' has already been defined.";
		carl::Variable var = carl::newArithmeticVariable(name, carl::SortManager::getInstance().interpretedType(sort), true);
		state->var_theory.sym.add(name, var);
		break;
	}
	case ExpressionType::UNINTERPRETED: {
		state->handler->error() << "Only variables of type \"Bool\", \"Int\" or \"Real\" are allowed!";
		break;
	}
	default:
		state->handler->error() << "Only variables of type \"Bool\", \"Int\" or \"Real\" are allowed!";
	}
	//callHandler(&InstructionHandler::declareConst, name, sort);
}
void SMTLIBParser::declareFun(const std::string& name, const std::vector<carl::Sort>& args, const carl::Sort& sort) {
	if (state->handler->printInstruction()) handler->regular() << "(declare-fun " << name << " () " << sort << ")" << std::endl;
	assert(state->isSymbolFree(name));
	switch (TypeOfTerm::get(sort)) {
	case ExpressionType::BOOLEAN: {
		if (args.size() == 0) {
			carl::Variable var = carl::newBooleanVariable(name, true);
			state->var_bool.sym.add(name, var);
			callHandler(&InstructionHandler::declareFun, var);
		} else {
			state->funmap_ufbool.add(name, carl::newUninterpretedFunction(name, args, sort));
		}
		break;
	}
	case ExpressionType::THEORY: {
		if (args.size() == 0) {
			carl::Variable var = carl::newArithmeticVariable(name, carl::SortManager::getInstance().interpretedType(sort), true);
			state->var_theory.sym.add(name, var);
			callHandler(&InstructionHandler::declareFun, var);
		} else {
			state->funmap_uftheory.add(name, carl::newUninterpretedFunction(name, args, sort));
		}
		break;
	}
	case ExpressionType::UNINTERPRETED: {
		if (args.size() == 0) {
			carl::Variable var = carl::newVariable(name, carl::VariableType::VT_UNINTERPRETED);
			auto v = carl::UVariable(var, sort);
			state->var_uninterpreted.sym.add(name, v);
			callHandler(&InstructionHandler::declareFun, var);
		} else {
			auto uf = carl::newUninterpretedFunction(name, args, sort);
			state->funmap_uf.add(name, uf);
		}
		break;
	}
	default:
		handler->error() << "Only functions of with a defined return type are allowed!";
	}
}
void SMTLIBParser::declareSort(const std::string& name, const unsigned& arity) {
	if (state->handler->printInstruction()) handler->regular() << "(declare-sort " << name << " " << arity << ")" << std::endl;
	if (!carl::SortManager::getInstance().declare(name, arity)) {
		state->handler->error() << "A sort " << name << " with arity " << arity << " has already been declared.";
	}
	callHandler(&InstructionHandler::declareSort, name, arity);
}
void SMTLIBParser::defineFun(const std::string& name, const std::vector<carl::Variable>& args, const carl::Sort& sort, const Argument& term) {
	if (state->handler->printInstruction()) handler->regular() << "(define-fun " << name << " () " << term << ")" << std::endl;
	state->popScope();
	switch (TypeOfTerm::get(sort)) {
	case ExpressionType::BOOLEAN:
		if (TypeOfTerm::get(term) != ExpressionType::BOOLEAN) {
			state->handler->error() << "The return type of \"" << name << "\" was given as Bool, but the parsed expression is a polynomial.";
			return;
		}
		if (args.size() == 0) {
			state->bind_bool.sym.add(name, boost::get<FormulaT>(term));
		} else {
			state->funmap_bool.add(name, std::make_tuple(name, args, boost::get<FormulaT>(term)));
		}
		break;
	case ExpressionType::THEORY:
		if (TypeOfTerm::get(term) != ExpressionType::THEORY) {
			state->handler->error() << "The return type of \"" << name << "\" was given as a theory type, but the parsed expression is a formula.";
			return;
		}
		for (const carl::Variable& v: args) {
			if (TypeOfTerm::get(v) != ExpressionType::THEORY) {
				state->handler->error() << "The argument " << carl::VariablePool::getInstance().getName(v) << " of " << name << " is Bool. For theory functions, only theory arguments are supported.";
				return;
			}
		}
		if (args.size() == 0) {
			state->bind_theory.sym.add(name, boost::get<Poly>(term));
		} else {
			state->funmap_theory.add(name, std::make_tuple(name, args, boost::get<Poly>(term)));
		}
		break;
	case ExpressionType::UNINTERPRETED:
		state->handler->error() << "Functions of uninterpreted type are not allowed!";
		break;
	default:
		state->handler->error() << "Unsupported function return type.";
	}

	//callHandler(&InstructionHandler::defineFun, name, args, sort, term);
}
void SMTLIBParser::defineSort(const std::string& name, const std::vector<std::string>& args, const carl::Sort& sort) {
	clearSortParameters();
	if (state->handler->printInstruction()) handler->regular() << "(define-sort " << name << " () " << sort << ")" << std::endl;
	if (!carl::SortManager::getInstance().define(name, args, sort)) {
		state->handler->error() << "A sort " << name << " has already been defined.";
	}
	callHandler(&InstructionHandler::defineSort, name, args, sort);
}
void SMTLIBParser::exit() {
	this->mInputStream->setstate(std::ios::eofbit);
	if (state->handler->printInstruction()) handler->regular() << "(exit)" << std::endl;
	callHandler(&InstructionHandler::exit);
}
void SMTLIBParser::getAssertions() {
	if (state->handler->printInstruction()) handler->regular() << "(get-assertions)" << std::endl;
	callHandler(&InstructionHandler::getAssertions);
}
void SMTLIBParser::getAssignment() {
	if (state->handler->printInstruction()) handler->regular() << "(get-assignment)" << std::endl;
	callHandler(&InstructionHandler::getAssignment);
}
void SMTLIBParser::getInfo(const std::string& key) {
	if (state->handler->printInstruction()) handler->regular() << "(get-info :" << key << ")" << std::endl;
	callHandler(&InstructionHandler::getInfo, key);
}
void SMTLIBParser::getOption(const std::string& key) {
	if (state->handler->printInstruction()) handler->regular() << "(get-option " << key << ")" << std::endl;
	callHandler(&InstructionHandler::getOption, key);
}
void SMTLIBParser::getProof() {
	if (state->handler->printInstruction()) handler->regular() << "(get-proof)" << std::endl;
	callHandler(&InstructionHandler::getProof);
}
void SMTLIBParser::getUnsatCore() {
	if (state->handler->printInstruction()) handler->regular() << "(get-unsat-core)" << std::endl;
	callHandler(&InstructionHandler::getUnsatCore);
}
void SMTLIBParser::getValue(const std::vector<carl::Variable>& vars) {
	if (state->handler->printInstruction()) handler->regular() << "(get-value)" << std::endl;
	std::vector<carl::Variable> carlVars;
	carlVars.reserve(vars.size());
	for (auto v: vars) carlVars.push_back(v);
	callHandler(&InstructionHandler::getValue, carlVars);
}
void SMTLIBParser::pop(const unsigned& n) {
	if (state->handler->printInstruction()) handler->regular() << "(pop " << n << ")" << std::endl;
	callHandler(&InstructionHandler::pop, n);
}
void SMTLIBParser::push(const unsigned& n) {
	if (state->handler->printInstruction()) handler->regular() << "(push " << n << ")" << std::endl;
	callHandler(&InstructionHandler::push, n);
}
void SMTLIBParser::setInfo(const Attribute& attribute) {
	if (state->handler->printInstruction()) handler->regular() << "(set-info :" << attribute << ")" << std::endl;
	callHandler(&InstructionHandler::setInfo, attribute);
}
void SMTLIBParser::setLogic(const smtrat::Logic& l) {
	state->mLogic = l;
	if (state->handler->printInstruction()) handler->regular() << "(set-logic " << l << ")" << std::endl;
	callHandler(&InstructionHandler::setLogic, l);
}
void SMTLIBParser::setOption(const Attribute& option) {
	if (state->handler->printInstruction()) handler->regular() << "(set-option " << option << ")" << std::endl;
	callHandler(&InstructionHandler::setOption, option);
}

carl::Variable SMTLIBParser::addQuantifiedVariable(const std::string& _name, const boost::optional<carl::VariableType>& type) {
	std::string name = _name;
	for (unsigned id = 1; !state->isSymbolFree(name, false); id++) {
		name = _name + "_q" + std::to_string(id);
	}
	if (type.is_initialized()) {
		switch (TypeOfTerm::get(type.get())) {
			case ExpressionType::BOOLEAN: {
				carl::Variable v = carl::newBooleanVariable(name);
				state->var_bool.sym.remove(_name);
				state->var_bool.sym.add(_name, v);
				return v;
			}
			case ExpressionType::THEORY: {
				carl::Variable v = carl::newArithmeticVariable(name, type.get());
				state->var_theory.sym.remove(_name);
				state->var_theory.sym.add(_name, v);
				return v;
			}
			default: { // case ExpressionType::UNINTERPRETED
				state->handler->error() << "Tried to quantify over an uninterpreted type.";
				assert(false);
				return carl::Variable::NO_VARIABLE;
			}
		}
	} else if (state->var_bool.sym.find(_name) != nullptr) {
		carl::Variable v = carl::newBooleanVariable(name);
		state->var_bool.sym.remove(_name);
		state->var_bool.sym.add(_name, v);
		return v;
	} else if (state->var_theory.sym.find(_name) != nullptr) {
		carl::Variable v = carl::newArithmeticVariable(name, state->var_theory.sym.at(_name).getType());
		state->var_theory.sym.remove(_name);
		state->var_theory.sym.add(_name, v);
		return v;
	} else {
		state->handler->error() << "Tried to quantify <" << _name << "> but no type could be inferred.";
		return carl::Variable::NO_VARIABLE;
	}
}

carl::Variable SMTLIBParser::addVariableBinding(const std::pair<std::string, carl::Sort>& b) {
	assert(state->isSymbolFree(b.first));
	switch (TypeOfTerm::get(b.second)) {
	case ExpressionType::BOOLEAN: {
		carl::Variable v = carl::VariablePool::getInstance().getFreshVariable(b.first, carl::VariableType::VT_BOOL);
		state->bind_bool.sym.add(b.first, FormulaT(v));
		return v;
	}
	case ExpressionType::THEORY: {
		carl::Variable v = carl::VariablePool::getInstance().getFreshVariable(b.first, carl::SortManager::getInstance().interpretedType(b.second));
		state->bind_theory.sym.add(b.first, Poly(v));
		return v;
	}
	case ExpressionType::UNINTERPRETED:
		state->handler->error() << "Tried to bind a uninterpreted variable.";
		return carl::Variable::NO_VARIABLE;
		break;
	default:
		assert(false);
		return carl::Variable::NO_VARIABLE;
	}
}

}
}
