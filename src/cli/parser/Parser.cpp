#include "Parser.h"

#include <cassert>
#include <iostream>
#include <limits>
#include <set>

#include "../../lib/ConstraintPool.h"
#include "../../lib/Formula.h"
#include "../../lib/UFInstancesManager.h"
#include "../../lib/UFManager.h"
#include "lib/FormulaPool.h"
#include "carl/util/debug.h"

namespace smtrat {
namespace parser {

SMTLIBParser::SMTLIBParser(InstructionHandler* ih, bool queueInstructions, bool debug):
	handler(ih),
	queueInstructions(queueInstructions)
{
	var_bool.sym.name("declared boolean variable");
	var_theory.sym.name("declared theory variable");
	bind_bool.sym.name("bound boolean variable");
	bind_theory.sym.name("bound theory variable");

	boundary = &qi::no_skip[(qi::space | qi::char_(")"))];

	var = var_bool | var_theory;
	var.name("variable");

	quantifiedVar = ("(" >> symbol >> -domain >> ")")[qi::_val = px::bind(&SMTLIBParser::addQuantifiedVariable, px::ref(*this), qi::_1, qi::_2)];
	quantifiedVar.name("quantified variable");

	sortedVar = "(" >> symbol >> sort >> ")";
	sortedVar.name("sorted variable");

	value = qi::bool_ | symbol | string | decimal | integral;
	value.name("value");
	attribute = (keyword > -value)[qi::_val = px::construct<Attribute>(qi::_1, qi::_2)];
	attribute.name("attribute");

	symlist = *symbol;
	symlist.name("symbol list");

	bindlist = +(qi::lit("(") > binding > qi::lit(")"));
	bindlist.name("binding list");
	binding = symbol[qi::_a = qi::_1] > (
			polynomial[px::bind(&SMTLIBParser::addTheoryBinding, px::ref(*this), qi::_a, qi::_1)]
		|	formula[px::bind(&SMTLIBParser::addBooleanBinding, px::ref(*this), qi::_a, qi::_1)]
		|	uninterpreted[px::bind(&SMTLIBParser::addUninterpretedBinding, px::ref(*this), qi::_a, qi::_1)]
	);
	binding.name("binding");
	
	fun_definition = symbol[px::bind(&SMTLIBParser::pushScope, px::ref(*this)), qi::_a = qi::_1] > "(" > 
		*(sortedVar[px::push_back(qi::_b, px::bind(&SMTLIBParser::addVariableBinding, px::ref(*this), qi::_1))]) 
		> ")" > (sort > fun_argument)[px::bind(&SMTLIBParser::defineFun, px::ref(*this), qi::_a, qi::_b, qi::_1, qi::_2)];
	fun_definition.name("function definition");
	
	uninterpreted = (
			var_uninterpreted[qi::_val = qi::_1]
		|	bind_uninterpreted[qi::_val = qi::_1]
		|	(qi::lit("(") >> funmap_uf >> fun_arguments >> qi::lit(")"))[qi::_val = px::bind(&SMTLIBParser::applyUninterpretedFunction, px::ref(*this), qi::_1, qi::_2)]
	);
	uninterpreted.name("uninterpreted argument");
	fun_argument = (formula | polynomial | uninterpreted);
	fun_argument.name("function argument");
	fun_arguments = *(fun_argument);
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


	formula = 
			(bind_bool >> boundary)[qi::_val = qi::_1]
		|	(var_bool >> boundary)[qi::_val = px::bind(&newBoolean, qi::_1)]
		|	qi::lit("true")[qi::_val = px::bind(&trueFormula)]
		|	qi::lit("false")[qi::_val = px::bind(&falseFormula)]
		|	("(" >> formula_op >> ")")[qi::_val = qi::_1]
	;
	formula.name("formula");
	
	formula_list = +formula;
	formula_list.name("formula list");
	formula_op =
				((op_bool >> formula_list)[qi::_val = px::bind(&SMTLIBParser::mkFormula, px::ref(*this), qi::_1, qi::_2)])
			|	(relation >> polynomial >> polynomial)[qi::_val = px::bind(&SMTLIBParser::mkConstraint, px::ref(*this), qi::_2, qi::_3, qi::_1)]
			|	((qi::lit("=") >> uninterpreted >> uninterpreted)[qi::_val = px::bind(&newEquality, qi::_1, qi::_2, false)])
			|	(qi::lit("as")[px::bind(&SMTLIBParser::errorMessage, px::ref(*this), "\"as\" is not supported."), qi::_pass = false] > symbol > symbol)
			|	(qi::lit("distinct")[px::bind(&SMTLIBParser::errorMessage, px::ref(*this), "\"distinct\" is not supported."),qi::_pass = false] > +formula)
			|	(qi::lit("not") > formula[qi::_val = px::bind(&newNegation, qi::_1)])
			|	((qi::lit("implies") | "=>") > formula > formula)[qi::_val = px::bind(newImplication, qi::_1, qi::_2)]
			|	(qi::lit("let")[px::bind(&SMTLIBParser::pushScope, px::ref(*this))]
				> ("(" > bindlist > ")" > formula)[px::bind(&SMTLIBParser::popScope, px::ref(*this)), qi::_val = qi::_1])
			|	(qi::lit("exists")[px::bind(&SMTLIBParser::pushScope, px::ref(*this))] > "(" > *quantifiedVar > ")" > formula)[qi::_val = px::bind(&newQuantifier, EXISTS, qi::_1, qi::_2), px::bind(&SMTLIBParser::popScope, px::ref(*this))]
			|	(qi::lit("forall")[px::bind(&SMTLIBParser::pushScope, px::ref(*this))] > "(" > *quantifiedVar > ")" > formula)[qi::_val = px::bind(&newQuantifier, FORALL, qi::_1, qi::_2), px::bind(&SMTLIBParser::popScope, px::ref(*this))]
			|	("ite" >> (formula >> formula >> formula)[qi::_val = px::bind(&newIte, qi::_1, qi::_2, qi::_3)])
			|	(("!" > formula > *attribute)[px::bind(&annotateFormula, qi::_1, qi::_2), qi::_val = qi::_1])
			|	((funmap_bool >> fun_arguments)[qi::_val = px::bind(&SMTLIBParser::applyBooleanFunction, px::ref(*this), qi::_1, qi::_2)])
			|	((funmap_ufbool >> fun_arguments)[qi::_val = px::bind(&SMTLIBParser::applyUninterpretedBooleanFunction, px::ref(*this), qi::_1, qi::_2)])
	;
	formula_op.name("formula operation");

	polynomial_op = op_theory >> +polynomial;
	polynomial_op.name("polynomial operation");
	polynomial_ite = qi::lit("ite") >> (formula >> polynomial >> polynomial)[qi::_val = px::bind(&SMTLIBParser::mkIteInExpr, px::ref(*this), qi::_1, qi::_2, qi::_3)];
	polynomial_ite.name("polynomial if-then-else");
	polynomial_fun = (funmap_theory >> fun_arguments)[qi::_val = px::bind(&SMTLIBParser::applyTheoryFunction, px::ref(*this), qi::_1, qi::_2)];
	polynomial_fun.name("theory function");
	polynomial_uf = (funmap_uftheory >> fun_arguments)[qi::_val = px::bind(&SMTLIBParser::applyUninterpretedTheoryFunction, px::ref(*this), qi::_1, qi::_2)];
	polynomial_uf.name("uninterpreted theory function");
	polynomial =
			(bind_theory >> boundary)
		|	(var_theory >> boundary)
		|	decimal
		|	integral
		|	("(" >> (
				polynomial_ite
			|	polynomial_op
			|	polynomial_fun
			|	polynomial_uf
		) >> ")")
	;
	polynomial.name("polynomial");

	main = *cmd > qi::eoi;
	main.name("SMTLib File");

	qi::on_error<qi::fail>(main, errorHandler(px::ref(*this), qi::_1, qi::_2, qi::_3, qi::_4));

	if (debug) {
		qi::on_success(bindlist, successHandler(px::ref(*this), px::ref(bindlist), qi::_val, qi::_1, qi::_2));
		qi::on_success(polynomial, successHandler(px::ref(*this), px::ref(polynomial), qi::_val, qi::_1, qi::_2));
		qi::on_success(polynomial_op, successHandler(px::ref(*this), px::ref(polynomial_op), qi::_val, qi::_1, qi::_2));
		qi::on_success(formula, successHandlerPtr(px::ref(*this), px::ref(formula), qi::_val, qi::_1, qi::_2));
		qi::on_success(formula_op, successHandlerPtr(px::ref(*this), px::ref(formula_op), qi::_val, qi::_1, qi::_2));
		qi::on_success(cmd, successHandler(px::ref(*this), px::ref(cmd), qi::_val, qi::_1, qi::_2));
		qi::on_success(main, successHandler(px::ref(*this), px::ref(main), qi::_val, qi::_1, qi::_2));
	}
}

bool SMTLIBParser::parse(std::istream& in, const std::string&) {
	in.unsetf(std::ios::skipws);
	mInputStream = &in;
	BaseIteratorType basebegin(in);
	Iterator begin(basebegin);
	Iterator end;
	return qi::phrase_parse(begin, end, main, skipper);
}

void SMTLIBParser::add(const Formula* f) {
	if (this->handler->printInstruction()) handler->regular() << "(assert " << *f << ")" << std::endl;
	assert(f != nullptr);
	if (!mTheoryIteBindings.empty()) {
		// There have been theory ite expressions within this formula.
		// We add the formulas from mTheoryIteBindings to the formula.
		mTheoryIteBindings.insert(f);
		f = newFormula(smtrat::AND, std::move(mTheoryIteBindings));
		mTheoryIteBindings.clear();
	}
	if (!mUninterpretedEqualities.empty()) {
		// There have been uninterpreted expressions within this formula.
		// We add the formulas from mUninterpretedExpressions to the formula.
		mUninterpretedEqualities.insert(f);
		f = newFormula(smtrat::AND, std::move(mUninterpretedEqualities));
		mUninterpretedEqualities.clear();
	}
	
	callHandler(&InstructionHandler::add, f);
}
void SMTLIBParser::check() {
	if (this->handler->printInstruction()) handler->regular() << "(check-sat)" << std::endl;
	callHandler(&InstructionHandler::check);
}
void SMTLIBParser::declareConst(const std::string& name, const Sort& sort) {
	if (this->handler->printInstruction()) handler->regular() << "(declare-const " << name << " " << sort << ")" << std::endl;
	assert(this->isSymbolFree(name));
	switch (TypeOfTerm::get(sort)) {
	case ExpressionType::BOOLEAN: {
		if (this->var_bool.sym.find(name) != nullptr) handler->warn() << "a boolean variable with name '" << name << "' has already been defined.";
		carl::Variable var = newBooleanVariable(name, true);
		this->var_bool.sym.add(name, var);
		break;
	}
	case ExpressionType::THEORY: {
		if (this->var_theory.sym.find(name) != nullptr) handler->warn() << "a theory variable with name '" << name << "' has already been defined.";
		carl::Variable var = newArithmeticVariable(name, SortManager::getInstance().interpretedType(sort), true);
		this->var_theory.sym.add(name, var);
		break;
	}
	case ExpressionType::UNINTERPRETED: {
		handler->error() << "Only variables of type \"Bool\", \"Int\" or \"Real\" are allowed!";
		break;
	}
	default:
		handler->error() << "Only variables of type \"Bool\", \"Int\" or \"Real\" are allowed!";
	}
	//callHandler(&InstructionHandler::declareConst, name, sort);
}
void SMTLIBParser::declareFun(const std::string& name, const std::vector<Sort>& args, const Sort& sort) {
	if (this->handler->printInstruction()) handler->regular() << "(declare-fun " << name << " () " << sort << ")" << std::endl;
	assert(this->isSymbolFree(name));
	switch (TypeOfTerm::get(sort)) {
	case ExpressionType::BOOLEAN: {
		if (args.size() == 0) {
			carl::Variable var = newBooleanVariable(name, true);
			this->var_bool.sym.add(name, var);
			callHandler(&InstructionHandler::declareFun, var);
		} else {
			this->funmap_ufbool.add(name, newUninterpretedFunction(name, args, sort));
		}
		break;
	}
	case ExpressionType::THEORY: {
		if (args.size() == 0) {
			carl::Variable var = newArithmeticVariable(name, SortManager::getInstance().interpretedType(sort), true);
			this->var_theory.sym.add(name, var);
			callHandler(&InstructionHandler::declareFun, var);
		} else {
			this->funmap_uftheory.add(name, newUninterpretedFunction(name, args, sort));
		}
		break;
	}
	case ExpressionType::UNINTERPRETED: {
		if (args.size() == 0) {
			carl::Variable var = newVariable(name, carl::VariableType::VT_UNINTERPRETED);
			auto v = UVariable(var, sort);
			this->var_uninterpreted.sym.add(name, v);
			std::cout << "Registering " << name << " -> " << v << std::endl;
			callHandler(&InstructionHandler::declareFun, var);
		} else {
			auto uf = newUninterpretedFunction(name, args, sort);
			std::cout << "Registering " << uf << std::endl;
			this->funmap_uf.add(name, uf);
		}
		break;
	}
	default:
		handler->error() << "Only functions of with a defined return type are allowed!";
	}
}
void SMTLIBParser::declareSort(const std::string& name, const unsigned& arity) {
	if (this->handler->printInstruction()) handler->regular() << "(declare-sort " << name << " " << arity << ")" << std::endl;
	if (!SortManager::getInstance().declare(name, arity)) {
		this->handler->error() << "A sort " << name << " with arity " << arity << " has already been declared.";
	}
	callHandler(&InstructionHandler::declareSort, name, arity);
}
void SMTLIBParser::defineFun(const std::string& name, const std::vector<carl::Variable>& args, const Sort& sort, const Argument& term) {
	if (this->handler->printInstruction()) handler->regular() << "(define-fun " << name << " () " << term << ")" << std::endl;
	this->popScope();
	switch (TypeOfTerm::get(sort)) {
	case ExpressionType::BOOLEAN:
		if (TypeOfTerm::get(term) != ExpressionType::BOOLEAN) {
			this->handler->error() << "The return type of \"" << name << "\" was given as Bool, but the parsed expression is a polynomial.";
			return;
		}
		if (args.size() == 0) {
			this->bind_bool.sym.add(name, boost::get<const Formula*>(term));
		} else {
			this->funmap_bool.add(name, std::make_tuple(name, args, boost::get<const Formula*>(term)));
		}
		break;
	case ExpressionType::THEORY:
		if (TypeOfTerm::get(term) != ExpressionType::THEORY) {
			this->handler->error() << "The return type of \"" << name << "\" was given as a theory type, but the parsed expression is a formula.";
			return;
		}
		for (const carl::Variable& v: args) {
			if (TypeOfTerm::get(v) != ExpressionType::THEORY) {
				this->handler->error() << "The argument " << carl::VariablePool::getInstance().getName(v) << " of " << name << " is Bool. For theory functions, only theory arguments are supported.";
				return;
			}
		}
		if (args.size() == 0) {
			this->bind_theory.sym.add(name, boost::get<Polynomial>(term));
		} else {
			this->funmap_theory.add(name, std::make_tuple(name, args, boost::get<Polynomial>(term)));
		}
		break;
	case ExpressionType::UNINTERPRETED:
		handler->error() << "Functions of uninterpreted type are not allowed!";
		break;
	default:
		handler->error() << "Unsupported function return type.";
	}

	//callHandler(&InstructionHandler::defineFun, name, args, sort, term);
}
void SMTLIBParser::defineSort(const std::string& name, const std::vector<std::string>& args, const Sort& sort) {
	clearSortParameters();
	if (this->handler->printInstruction()) handler->regular() << "(define-sort " << name << " () " << sort << ")" << std::endl;
	if (!SortManager::getInstance().define(name, args, sort)) {
		this->handler->error() << "A sort " << name << " has already been defined.";
	}
	callHandler(&InstructionHandler::defineSort, name, args, sort);
}
void SMTLIBParser::exit() {
	this->mInputStream->setstate(std::ios::eofbit);
	if (this->handler->printInstruction()) handler->regular() << "(exit)" << std::endl;
	callHandler(&InstructionHandler::exit);
}
void SMTLIBParser::getAssertions() {
	if (this->handler->printInstruction()) handler->regular() << "(get-assertions)" << std::endl;
	callHandler(&InstructionHandler::getAssertions);
}
void SMTLIBParser::getAssignment() {
	if (this->handler->printInstruction()) handler->regular() << "(get-assignment)" << std::endl;
	callHandler(&InstructionHandler::getAssignment);
}
void SMTLIBParser::getInfo(const std::string& key) {
	if (this->handler->printInstruction()) handler->regular() << "(get-info :" << key << ")" << std::endl;
	callHandler(&InstructionHandler::getInfo, key);
}
void SMTLIBParser::getOption(const std::string& key) {
	if (this->handler->printInstruction()) handler->regular() << "(get-option " << key << ")" << std::endl;
	callHandler(&InstructionHandler::getOption, key);
}
void SMTLIBParser::getProof() {
	if (this->handler->printInstruction()) handler->regular() << "(get-proof)" << std::endl;
	callHandler(&InstructionHandler::getProof);
}
void SMTLIBParser::getUnsatCore() {
	if (this->handler->printInstruction()) handler->regular() << "(get-unsat-core)" << std::endl;
	callHandler(&InstructionHandler::getUnsatCore);
}
void SMTLIBParser::getValue(const std::vector<carl::Variable>& vars) {
	if (this->handler->printInstruction()) handler->regular() << "(get-value)" << std::endl;
	std::vector<carl::Variable> carlVars;
	carlVars.reserve(vars.size());
	for (auto v: vars) carlVars.push_back(v);
	callHandler(&InstructionHandler::getValue, carlVars);
}
void SMTLIBParser::pop(const unsigned& n) {
	if (this->handler->printInstruction()) handler->regular() << "(pop " << n << ")" << std::endl;
	callHandler(&InstructionHandler::pop, n);
}
void SMTLIBParser::push(const unsigned& n) {
	if (this->handler->printInstruction()) handler->regular() << "(push " << n << ")" << std::endl;
	callHandler(&InstructionHandler::push, n);
}
void SMTLIBParser::setInfo(const Attribute& attribute) {
	if (this->handler->printInstruction()) handler->regular() << "(set-info :" << attribute << ")" << std::endl;
	callHandler(&InstructionHandler::setInfo, attribute);
}
void SMTLIBParser::setLogic(const smtrat::Logic& l) {
	this->mLogic = l;
	if (this->handler->printInstruction()) handler->regular() << "(set-logic " << l << ")" << std::endl;
	callHandler(&InstructionHandler::setLogic, l);
}
void SMTLIBParser::setOption(const Attribute& option) {
	if (this->handler->printInstruction()) handler->regular() << "(set-option " << option << ")" << std::endl;
	callHandler(&InstructionHandler::setOption, option);
}

#if 1

const Formula* SMTLIBParser::mkConstraint(const Polynomial& lhs, const Polynomial& rhs, Relation rel) {
	Polynomial p = lhs - rhs;
	std::set<carl::Variable> pVars = p.gatherVariables();
	std::vector<carl::Variable> vars;
	while (!pVars.empty()) {
		auto it = this->mTheoryItes.find(*pVars.begin());
		pVars.erase(pVars.begin());
		if (it != this->mTheoryItes.end()) {
			std::get<1>(it->second).gatherVariables(pVars);
			std::get<2>(it->second).gatherVariables(pVars);
			vars.push_back(it->first);
		}
	}
	std::size_t n = vars.size();
	if (n == 0) {
		// There are no ITEs.
		const Constraint* cons = newConstraint(p, rel);
		return newFormula(cons);
	} else if (n < 4) {
		// There are only a few ITEs, hence we expand them here directly to 2^n cases.
		// 2^n Polynomials with values substituted.
		std::vector<Polynomial> polys({p});
		// 2^n Formulas collecting the conditions.
		std::vector<PointerSet<Formula>> conds(1 << n);
		unsigned repeat = 1 << (n-1);
		for (auto v: vars) {
			auto t = this->mTheoryItes[v];
			std::vector<Polynomial> ptmp;
			for (auto& p: polys) {
				// Substitute both possibilities for this ITE.
				ptmp.push_back(p.substitute(v, std::get<1>(t)));
				ptmp.push_back(p.substitute(v, std::get<2>(t)));
			}
			std::swap(polys, ptmp);
			// Add the conditions at the appropriate positions.
			const Formula* f[2]= { std::get<0>(t), newNegation(std::get<0>(t)) };
			for (size_t i = 0; i < (size_t)(1 << n); i++) {
				conds[i].insert(f[0]);
				if ((i+1) % repeat == 0) std::swap(f[0], f[1]);
			}
			repeat /= 2;
		}
		// Now combine everything: (and (=> (and conditions) constraint) ...)
		PointerSet<Formula> subs;
		for (unsigned i = 0; i < polys.size(); i++) {
			subs.insert(newImplication(newFormula(Type::AND, conds[i]), newFormula(newConstraint(polys[i], rel))));
		}
		auto res = newFormula(Type::AND, subs);
		return res;
	} else {
		// There are many ITEs, we keep the auxiliary variables.
		for (auto v: vars) {
			auto t = this->mTheoryItes[v];
			const Formula* consThen = newFormula(newConstraint(Polynomial(v) - std::get<1>(t), Relation::EQ));
			const Formula* consElse = newFormula(newConstraint(Polynomial(v) - std::get<2>(t), Relation::EQ));

			mTheoryIteBindings.emplace(newImplication(std::get<0>(t), consThen));
			mTheoryIteBindings.emplace(newImplication(newNegation(std::get<0>(t)), consElse));
		}
		const Constraint* cons = newConstraint(p, rel);
		return newFormula(cons);
	}
}

Polynomial SMTLIBParser::mkIteInExpr(const Formula* _condition, Polynomial& _then, Polynomial& _else) {
	
	if (_then == _else) return _then;
	if (_condition == falseFormula()) return _else;
	if (_condition == trueFormula()) return _then;
	
	carl::Variable auxVar = (mLogic == Logic::QF_LIA || mLogic == Logic::QF_NIA) ? newAuxiliaryIntVariable() : newAuxiliaryRealVariable();

	mTheoryItes[auxVar] = std::make_tuple(_condition, _then, _else);
	return Polynomial(auxVar);
}

#else

const Formula* SMTLIBParser::mkConstraint(const Polynomial& lhs, const Polynomial& rhs, Relation rel) {
	const Constraint* cons = newConstraint(lhs-rhs, rel);
	return newFormula(cons);
}

Polynomial SMTLIBParser::mkIteInExpr(const Formula* _condition, Polynomial& _then, Polynomial& _else) {
	
	if (_then == _else) return _then;
	if (_condition == falseFormula()) return _else;
	if (_condition == trueFormula()) return _then;
	
	carl::Variable auxVar = (mLogic == Logic::QF_LIA || mLogic == Logic::QF_NIA) ? newAuxiliaryIntVariable() : newAuxiliaryRealVariable();

	const Formula* consThen = mkConstraint(Polynomial(auxVar), _then, Relation::EQ);
	const Formula* consElse = mkConstraint(Polynomial(auxVar), _else, Relation::EQ);

	mTheoryIteBindings.emplace(newImplication(_condition, consThen));
	mTheoryIteBindings.emplace(newImplication(newNegation(_condition), consElse));
	return Polynomial(auxVar);
}

#endif

const smtrat::Formula* SMTLIBParser::mkFormula( smtrat::Type type, PointerSet<Formula>& _subformulas )
{
	assert(type == smtrat::AND || type == smtrat::OR || type == smtrat::XOR || type == smtrat::IFF);
	return newFormula(type, _subformulas);
}

carl::Variable SMTLIBParser::addQuantifiedVariable(const std::string& _name, const boost::optional<carl::VariableType>& type) {
	std::string name = _name;
	for (unsigned id = 1; !this->isSymbolFree(name, false); id++) {
		name = _name + "_q" + std::to_string(id);
	}
	if (type.is_initialized()) {
		switch (TypeOfTerm::get(type.get())) {
			case ExpressionType::BOOLEAN: {
				carl::Variable v = newBooleanVariable(name);
				this->var_bool.sym.remove(_name);
				this->var_bool.sym.add(_name, v);
				return v;
			}
			case ExpressionType::THEORY: {
				carl::Variable v = newArithmeticVariable(name, type.get());
				this->var_theory.sym.remove(_name);
				this->var_theory.sym.add(_name, v);
				return v;
			}
			default: { // case ExpressionType::UNINTERPRETED
				this->handler->error() << "Tried to quantify over an uninterpreted type.";
				assert(false);
				return carl::Variable::NO_VARIABLE;
			}
		}
	} else if (this->var_bool.sym.find(_name) != nullptr) {
		carl::Variable v = newBooleanVariable(name);
		this->var_bool.sym.remove(_name);
		this->var_bool.sym.add(_name, v);
		return v;
	} else if (this->var_theory.sym.find(_name) != nullptr) {
		carl::Variable v = newArithmeticVariable(name, this->var_theory.sym.at(_name).getType());
		this->var_theory.sym.remove(_name);
		this->var_theory.sym.add(_name, v);
		return v;
	} else {
		this->handler->error() << "Tried to quantify <" << _name << "> but no type could be inferred.";
		return carl::Variable::NO_VARIABLE;
	}
}

carl::Variable SMTLIBParser::addVariableBinding(const std::pair<std::string, Sort>& b) {
	assert(this->isSymbolFree(b.first));
	switch (TypeOfTerm::get(b.second)) {
	case ExpressionType::BOOLEAN: {
		carl::Variable v = carl::VariablePool::getInstance().getFreshVariable(b.first, carl::VariableType::VT_BOOL);
		bind_bool.sym.add(b.first, newBoolean(v));
		return v;
	}
	case ExpressionType::THEORY: {
		carl::Variable v = carl::VariablePool::getInstance().getFreshVariable(b.first, SortManager::getInstance().interpretedType(b.second));
		bind_theory.sym.add(b.first, Polynomial(v));
		return v;
	}
	case ExpressionType::UNINTERPRETED:
		this->handler->error() << "Tried to bind a uninterpreted variable.";
		return carl::Variable::NO_VARIABLE;
		break;
	default:
		assert(false);
		return carl::Variable::NO_VARIABLE;
	}
}

void SMTLIBParser::addTheoryBinding(std::string& _varName, Polynomial& _polynomial) {
	assert(this->isSymbolFree(_varName));
	bind_theory.sym.add(_varName, _polynomial);
}

void SMTLIBParser::addBooleanBinding(std::string& _varName, const Formula* _formula) {
	assert(this->isSymbolFree(_varName));
	bind_bool.sym.add(_varName, _formula);
}

void SMTLIBParser::addUninterpretedBinding(std::string& _varName, const UninterpretedType& _uninterpreted) {
	assert(this->isSymbolFree(_varName));
	bind_uninterpreted.sym.add(_varName, _uninterpreted);
}

bool SMTLIBParser::checkArguments(const std::string& name, const std::vector<carl::Variable>& types, const Arguments& args, std::map<carl::Variable, const Formula*>& boolAssignments, std::map<carl::Variable, Polynomial>& theoryAssignments) {
	if (types.size() != args.size()) {
		this->handler->error() << "The number of arguments for \"" << name << "\" does not match its declaration.";
		return false;
	}
	for (unsigned id = 0; id < types.size(); id++) {
		ExpressionType type = TypeOfTerm::get(types[id]);
		if (type != TypeOfTerm::get(args[id])) {
			this->handler->error() << "The type of argument " << (id+1) << " for \"" << name << "\" did not match the declaration.";
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

const smtrat::Formula* SMTLIBParser::applyBooleanFunction(const BooleanFunction& f, const Arguments& args) {
	std::map<carl::Variable, const Formula*> boolAssignments;
	std::map<carl::Variable, Polynomial> theoryAssignments;
	if (!checkArguments(std::get<0>(f), std::get<1>(f), args, boolAssignments, theoryAssignments)) {
		return nullptr;
	}
	return std::get<2>(f)->substitute(boolAssignments, theoryAssignments);
}
const smtrat::Formula* SMTLIBParser::applyUninterpretedBooleanFunction(const UninterpretedFunction& f, const Arguments& args) {
	carl::Variable v = newAuxiliaryBooleanVariable();
	mUninterpretedEqualities.insert(newFormula(std::move(UEquality(UVariable(v), applyUninterpretedFunction(f, args), false))));
	return newBoolean(v);
}
Polynomial SMTLIBParser::applyTheoryFunction(const TheoryFunction& f, const Arguments& args) {
	std::map<carl::Variable, const Formula*> boolAssignments;
	std::map<carl::Variable, Polynomial> theoryAssignments;
	if (!checkArguments(std::get<0>(f), std::get<1>(f), args, boolAssignments, theoryAssignments)) {
		return smtrat::Polynomial();
	}
	return std::get<2>(f).substitute(theoryAssignments);
}

Polynomial SMTLIBParser::applyUninterpretedTheoryFunction(const UninterpretedFunction& f, const Arguments& args) {
	assert(SortManager::getInstance().isInterpreted(f.codomain()));
	
	carl::Variable v = newAuxiliaryVariable(SortManager::getInstance().interpretedType(f.codomain()));
	mUninterpretedEqualities.insert(newFormula(std::move(UEquality(UVariable(v), applyUninterpretedFunction(f, args), false))));
	return Polynomial(v);
}

UFInstance SMTLIBParser::applyUninterpretedFunction(const UninterpretedFunction& f, const Arguments& args) {
	std::vector<UVariable> vars;
	for (auto v: args) {
		if (const Formula** f = boost::get<const Formula*>(&v)) {
			carl::Variable tmp = newAuxiliaryBooleanVariable();
			vars.push_back(UVariable(tmp));
			mUninterpretedEqualities.insert(newFormula(Type::AND, newBoolean(tmp), *f));
		} else if (Polynomial* p = boost::get<Polynomial>(&v)) {
			carl::Variable tmp = newAuxiliaryRealVariable();
			vars.push_back(UVariable(tmp));
			mUninterpretedEqualities.insert(newFormula(newConstraint(*p - tmp, Relation::EQ)));
		} else if (UVariable* uv = boost::get<UVariable>(&v)) {
			vars.push_back(*uv);
		} else if (UFInstance* uf = boost::get<UFInstance>(&v)) {
			carl::Variable tmp = newAuxiliaryUninterpretedVariable();
			vars.push_back(UVariable(tmp, uf->uninterpretedFunction().codomain()));
			mUninterpretedEqualities.insert(newFormula(std::move(UEquality(vars.back(), *uf, false))));
		}
	}
	return newUFInstance(f, vars);
}

}
}
