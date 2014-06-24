#include "Parser.h"

#include <cassert>
#include <iostream>
#include <limits>

#include "../../lib/ConstraintPool.h"
#include "../../lib/Formula.h"
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

	sortedVar = symbol >> domain;
	sortedVar.name("sorted variable");

	key = ":" > symbol;
	key.name("key");
	value = qi::bool_ | symbol | string | decimal | integral;
	value.name("value");
	attribute = key > -value;
	attribute.name("attribute");

	varlist = *var;
	varlist.name("variable list");

	symlist = *symbol;
	symlist.name("symbol list");

	bindlist = +(qi::lit("(") > binding > qi::lit(")"));
	bindlist.name("binding list");
	binding = symbol[qi::_a = qi::_1] > (
			polynomial[px::bind(&SMTLIBParser::addTheoryBinding, px::ref(*this), qi::_a, qi::_1)]
		|	formula[px::bind(&SMTLIBParser::addBooleanBinding, px::ref(*this), qi::_a, qi::_1)]
	);
	binding.name("binding");
	
	fun_definition = symbol[px::bind(&SMTLIBParser::pushVariableStack, px::ref(*this)), qi::_a = qi::_1] > "(" > 
		*("(" > sortedVar[px::push_back(qi::_b, px::bind(&SMTLIBParser::addVariableBinding, px::ref(*this), qi::_1))] > ")") 
		> ")" > (domain > (formula | polynomial))[px::bind(&SMTLIBParser::defineFun, px::ref(*this), qi::_a, qi::_b, qi::_1, qi::_2)];
	fun_definition.name("function definition");
	
	fun_arguments = *(formula | polynomial);
	fun_arguments.name("function arguments");
	
	cmd = "(" > (
			(qi::lit("assert") > formula > ")")[px::bind(&SMTLIBParser::add, px::ref(*this), qi::_1)]
		|	(qi::lit("check-sat") > ")")[px::bind(&SMTLIBParser::check, px::ref(*this))]
		|	(qi::lit("declare-const") > symbol > domain > ")")[px::bind(&SMTLIBParser::declareConst, px::ref(*this), qi::_1, qi::_2)]
		|	(qi::lit("declare-fun") > symbol > "(" > *domain > ")" > domain > ")")[px::bind(&SMTLIBParser::declareFun, px::ref(*this), qi::_1, qi::_2, qi::_3)]
		|	(qi::lit("declare-sort") > symbol > integral > ")")[px::bind(&SMTLIBParser::declareSort, px::ref(*this), qi::_1, qi::_2)]
		|	(qi::lit("define-fun") > fun_definition > ")")
		|	(qi::lit("define-sort") > symbol > "(" > symlist > ")" > symbol > ")")[px::bind(&SMTLIBParser::defineSort, px::ref(*this), qi::_1, qi::_2, qi::_3)]
		|	(qi::lit("exit") > ")")[px::bind(&SMTLIBParser::exit, px::ref(*this))]
		|	(qi::lit("get-assertions") > ")")[px::bind(&SMTLIBParser::getAssertions, px::ref(*this))]
		|	(qi::lit("get-assignment") > ")")[px::bind(&SMTLIBParser::getAssignment, px::ref(*this))]
		|	(qi::lit("get-info") > key > ")")[px::bind(&SMTLIBParser::getInfo, px::ref(*this), qi::_1)]
		|	(qi::lit("get-option") > key > ")")[px::bind(&SMTLIBParser::getOption, px::ref(*this), qi::_1)]
		|	(qi::lit("get-proof") > ")")[px::bind(&SMTLIBParser::getProof, px::ref(*this))]
		|	(qi::lit("get-unsat-core") > ")")[px::bind(&SMTLIBParser::getUnsatCore, px::ref(*this))]
		|	(qi::lit("get-value") > *var > ")")[px::bind(&SMTLIBParser::getValue, px::ref(*this), qi::_1)]
		|	(qi::lit("pop") > integral > ")")[px::bind(&SMTLIBParser::pop, px::ref(*this), qi::_1)]
		|	(qi::lit("push") > integral > ")")[px::bind(&SMTLIBParser::push, px::ref(*this), qi::_1)]
		|	(qi::lit("set-info") > key > value > ")")[px::bind(&SMTLIBParser::setInfo, px::ref(*this), qi::_1, qi::_2)]
		|	(qi::lit("set-logic") > logic > ")")[px::bind(&SMTLIBParser::setLogic, px::ref(*this), qi::_1)]
		|	(qi::lit("set-option") > key > value > ")")[px::bind(&SMTLIBParser::setOption, px::ref(*this), qi::_1, qi::_2)]
	);
	cmd.name("command");

	formula = 
			(bind_bool >> boundary)[qi::_val = qi::_1]
		|	(var_bool >> boundary)[qi::_val = px::bind(&SMTLIBParser::mkBoolean, px::ref(*this), qi::_1)]
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
			|	(qi::lit("as")[qi::_pass = false] > symbol > symbol)
			|	(qi::lit("not") > formula[qi::_val = px::bind(&newNegation, qi::_1)])
			|	((qi::lit("implies") | "=>") > formula > formula)[qi::_val = px::bind(newImplication, qi::_1, qi::_2)]
			|	(qi::lit("let")[px::bind(&SMTLIBParser::pushVariableStack, px::ref(*this))]
				> ("(" > bindlist > ")" > formula)[px::bind(&SMTLIBParser::popVariableStack, px::ref(*this)), qi::_val = qi::_1])
			|	("exists" > bindlist > formula)
			|	("forall" > bindlist > formula)
			|	("ite" >> (formula >> formula >> formula)[qi::_val = px::bind(&newIte, qi::_1, qi::_2, qi::_3)])
			|	(("!" > formula > *attribute)[px::bind(&annotateFormula, qi::_1, qi::_2), qi::_val = qi::_1])
			|	((funmap_bool >> fun_arguments)[qi::_val = px::bind(&applyBooleanFunction, qi::_1, qi::_2, std::bind(&InstructionHandler::error, this->handler))])
	;
	formula_op.name("formula operation");

	polynomial_op = op_theory >> +polynomial;
	polynomial_op.name("polynomial operation");
	polynomial_ite = qi::lit("ite") >> (formula >> polynomial >> polynomial)[qi::_val = px::bind(&SMTLIBParser::mkIteInExpr, px::ref(*this), qi::_1, qi::_2, qi::_3)];
	polynomial_ite.name("polynomial if-then-else");
	polynomial_fun = (funmap_theory >> fun_arguments)[qi::_val = px::bind(&applyTheoryFunction, qi::_1, qi::_2, std::bind(&InstructionHandler::error, this->handler))];
	polynomial_fun.name("theory function");
	polynomial =
			(bind_theory >> boundary)
		|	(var_theory >> boundary)
		|	decimal
		|	integral
		|	("(" >> (
				polynomial_ite
			|	polynomial_op
			|	polynomial_fun
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

bool SMTLIBParser::parse(std::istream& in, const std::string& filename) {
	in.unsetf(std::ios::skipws);
	mInputStream = &in;
	BaseIteratorType basebegin(in);
	Iterator begin(basebegin);
	Iterator end;
	return qi::phrase_parse(begin, end, main, skipper);
}

void SMTLIBParser::add(const Formula* f) {
	assert(f != nullptr);
	
	if (!mTheoryIteBindings.empty()) {
		// There have been theory ite expressions within this formula.
		// We add the formulas from mTheoryIteBindings to the formula.
		mTheoryIteBindings.insert(f);
		f = newFormula(smtrat::AND, std::move(mTheoryIteBindings));
		mTheoryIteBindings.clear();
	}
	
	if (this->handler->printInstruction()) handler->regular() << "(assert " << *f << ")" << std::endl;
	callHandler(&InstructionHandler::add, f);
}
void SMTLIBParser::check() {
	if (this->handler->printInstruction()) handler->regular() << "(check-sat)" << std::endl;
	callHandler(&InstructionHandler::check);
}
void SMTLIBParser::declareConst(const std::string& name, const carl::VariableType& sort) {
	assert(this->isSymbolFree(name));
	switch (sort) {
	case carl::VariableType::VT_BOOL: {
			if (this->var_bool.sym.find(name) != nullptr) handler->warn() << "a boolean variable with name '" << name << "' has already been defined.";
			carl::Variable var = newBooleanVariable(name, true);
			this->var_bool.sym.add(name, var);
			break;
		}
		break;
	case carl::VariableType::VT_INT:
	case carl::VariableType::VT_REAL: {
			if (this->var_theory.sym.find(name) != nullptr) handler->warn() << "a theory variable with name '" << name << "' has already been defined.";
			carl::Variable var = newArithmeticVariable(name, sort, true);
			this->var_theory.sym.add(name, var);
			break;
		}
	default:
		handler->error() << "Only variables of type \"Bool\", \"Int\" or \"Real\" are allowed!";
	}
	if (this->handler->printInstruction()) handler->regular() << "(declare-const " << name << " " << sort << ")" << std::endl;
	//callHandler(&InstructionHandler::declareConst, name, sort);
}
void SMTLIBParser::declareFun(const std::string& name, const std::vector<carl::VariableType>& args, const carl::VariableType& sort) {
	assert(this->isSymbolFree(name));
	assert(args.size() == 0);
	switch (TypeOfTerm::get(sort)) {
	case BOOLEAN: {
			if (this->var_bool.sym.find(name) != nullptr) handler->warn() << "a boolean variable with name '" << name << "' has already been defined.";
			carl::Variable var = newBooleanVariable(name, true);
			this->var_bool.sym.add(name, var);
			break;
		}
		break;
	case THEORY: {
			if (this->var_theory.sym.find(name) != nullptr) handler->warn() << "a theory variable with name '" << name << "' has already been defined.";
			carl::Variable var = newArithmeticVariable(name, sort, true);
			this->var_theory.sym.add(name, var);
			break;
		}
	default:
		handler->error() << "Only variables of type \"Bool\", \"Int\" or \"Real\" are allowed!";
	}
	if (this->handler->printInstruction()) handler->regular() << "(declare-fun " << name << " () " << sort << ")" << std::endl;
	//callHandler(&InstructionHandler::declareFun, name, args, sort);
}
void SMTLIBParser::declareSort(const std::string& name, const Rational& arity) {
	if (this->handler->printInstruction()) handler->regular() << "(declare-sort " << name << " " << arity << ")" << std::endl;
	callHandler(&InstructionHandler::declareSort, name, carl::toInt<unsigned>(arity));
}
void SMTLIBParser::defineFun(const std::string& name, const std::vector<carl::Variable>& args, const carl::VariableType& sort, const boost::variant<const Formula*, Polynomial>& term) {
	switch (TypeOfTerm::get(sort)) {
	case BOOLEAN:
		if (TypeOfTerm::get(term) != BOOLEAN) {
			this->handler->error() << "The return type of \"" << name << "\" was given as Bool, but the parsed expression is a polynomial.";
			return;
		}
		if (args.size() == 0) {
			this->bind_bool.sym.add(name, boost::get<const Formula*>(term));
		} else {
			this->funmap_bool.add(name, std::make_tuple(name, args, boost::get<const Formula*>(term)));
		}
		break;
	case THEORY:
		if (TypeOfTerm::get(term) != THEORY) {
			this->handler->error() << "The return type of \"" << name << "\" was given as a theory type, but the parsed expression is a formula.";
			return;
		}
		for (const carl::Variable& v: args) {
			if (TypeOfTerm::get(v) != THEORY) {
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
	default:
		handler->error() << "Unsupported function return type.";
	}
	this->popVariableStack();

	if (this->handler->printInstruction()) handler->regular() << "(define-fun " << name << " () " << term << ")" << std::endl;
	//callHandler(&InstructionHandler::defineFun, name, args, sort, term);
}
void SMTLIBParser::defineSort(const std::string& name, const std::vector<std::string>& args, const std::string& theory) {
	if (this->handler->printInstruction()) handler->regular() << "(define-sort " << name << " () " << theory << ")" << std::endl;
	callHandler(&InstructionHandler::defineSort, name, args, theory);
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
	std::vector<carl::Variable> carlVars;
	carlVars.reserve(vars.size());
	for (auto v: vars) carlVars.push_back(v);
	if (this->handler->printInstruction()) handler->regular() << "(get-value)" << std::endl;
	callHandler(&InstructionHandler::getValue, carlVars);
}
void SMTLIBParser::pop(const Rational& n) {
	if (this->handler->printInstruction()) handler->regular() << "(pop " << n << ")" << std::endl;
	callHandler(&InstructionHandler::pop, carl::toInt<unsigned>(n));
}
void SMTLIBParser::push(const Rational& n) {
	if (this->handler->printInstruction()) handler->regular() << "(push " << n << ")" << std::endl;
	callHandler(&InstructionHandler::push, carl::toInt<unsigned>(n));
}
void SMTLIBParser::setInfo(const std::string& key, const AttributeValue& val) {
	if (this->handler->printInstruction()) handler->regular() << "(set-info :" << key << " " << val << ")" << std::endl;
	callHandler(&InstructionHandler::setInfo, key, val);
}
void SMTLIBParser::setLogic(const smtrat::Logic& l) {
	this->mLogic = l;
	if (this->handler->printInstruction()) handler->regular() << "(set-logic " << l << ")" << std::endl;
	callHandler(&InstructionHandler::setLogic, l);
}
void SMTLIBParser::setOption(const std::string& key, const AttributeValue& val) {
	if (this->handler->printInstruction()) handler->regular() << "(set-option " << key << " " << val << ")" << std::endl;
	callHandler(&InstructionHandler::setOption, key, val);
}

#if 0

const Formula* SMTLIBParser::mkConstraint(const Polynomial& lhs, const Polynomial& rhs, Relation rel) {
	Polynomial p = lhs - rhs;
	///@todo check if variables from the ites vanish in the variables
	std::size_t n = this->mTheoryItes.size();
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
		for (auto it: this->mTheoryItes) {
			std::vector<Polynomial> ptmp;
			for (auto& p: polys) {
				// Substitute both possibilities for this ITE.
				ptmp.push_back(p.substitute(it.first, std::get<1>(it.second)));
				ptmp.push_back(p.substitute(it.first, std::get<2>(it.second)));
			}
			std::swap(polys, ptmp);
			// Add the conditions at the appropriate positions.
			const Formula* f[2]= { std::get<0>(it.second), newNegation(std::get<0>(it.second)) };
			for (unsigned i = 0; i < (1 << n); i++) {
				conds[i].insert(f[0]);
				if ((i+1) % repeat == 0) std::swap(f[0], f[1]);
			}
			repeat /= 2;
		}
		mTheoryItes.clear();
		// Now combine everything: (and (=> (and conditions) constraint) ...)
		PointerSet<Formula> subs;
		for (unsigned i = 0; i < polys.size(); i++) {
			subs.insert(newImplication(newFormula(Type::AND, conds[i]), newFormula(newConstraint(polys[i], rel))));
		}
		auto res = newFormula(Type::AND, subs);
		return res;
	} else {
		// There are many ITEs, we keep the auxiliary variables.
		for (auto it: this->mTheoryItes) {
			carl::Variable v = it.first;
			const Formula* consThen = newFormula(newConstraint(Polynomial(v) - std::get<1>(it.second), Relation::EQ));
			const Formula* consElse = newFormula(newConstraint(Polynomial(v) - std::get<2>(it.second), Relation::EQ));

			mTheoryIteBindings.emplace(newImplication(std::get<0>(it.second), consThen));
			mTheoryIteBindings.emplace(newImplication(newNegation(std::get<0>(it.second)), consElse));
		}
		mTheoryItes.clear();
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
	auto f =  newFormula(type, _subformulas);
	return f;
}

carl::Variable SMTLIBParser::addVariableBinding(const std::pair<std::string, carl::VariableType>& b) {
	assert(this->isSymbolFree(b.first));
	mVariableStack.top().emplace_back(b.first, b.second);
	carl::Variable v = carl::VariablePool::getInstance().getFreshVariable(b.first, b.second);
	switch (TypeOfTerm::get(b.second)) {
	case BOOLEAN:
		bind_bool.sym.add(b.first, newFormula(v));
		break;
	case THEORY:
		bind_theory.sym.add(b.first, Polynomial(v));
		break;
	}
	return v;
}

void SMTLIBParser::addTheoryBinding(std::string& _varName, Polynomial& _polynomial) {
	assert(this->isSymbolFree(_varName));
	mVariableStack.top().emplace_back(_varName, carl::VariableType::VT_REAL);
	bind_theory.sym.add(_varName, _polynomial);
}

void SMTLIBParser::addBooleanBinding(std::string& _varName, const Formula* _formula) {
	assert(this->isSymbolFree(_varName));
	mVariableStack.top().emplace_back(_varName, carl::VariableType::VT_BOOL);
	bind_bool.sym.add(_varName, _formula);
}

}
}
