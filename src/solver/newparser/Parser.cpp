#include "Parser.h"

#include <cassert>
#include <iostream>
#include <limits>

#include "../../lib/ConstraintPool.h"
#include "../../lib/Formula.h"
#include "lib/FormulaPool.h"

namespace smtrat {
namespace parser {

SMTLIBParser::SMTLIBParser(InstructionHandler* ih, bool queueInstructions):
	SMTLIBParser::base_type(main),
	handler(ih),
	queueInstructions(queueInstructions)
{
	boundary = &qi::no_skip[(qi::space | qi::char_(")"))];

	var = var_bool | var_theory;
	var.name("variable");

	key = ":" > symbol;
	key.name("key");
	value = qi::bool_ | symbol | decimal | integral;
	value.name("value");
	attribute = key > -value;
	attribute.name("attribute");

	varlist = *var;
	varlist.name("variable list");

	symlist = *symbol;
	symlist.name("symbol list");

	bindlist = +(lit("(") > binding > lit(")"));
	bindlist.name("binding list");
	binding = symbol[qi::_a = qi::_1] > (
			polynomial[px::bind(&SMTLIBParser::addTheoryBinding, px::ref(*this), qi::_a, qi::_1)]
		|	formula[px::bind(&SMTLIBParser::addBooleanBinding, px::ref(*this), qi::_a, qi::_1)]
	);
	binding.name("binding");
	
	cmd = "(" > (
			(lit("assert") > formula > ")")[px::bind(&SMTLIBParser::add, px::ref(*this), qi::_1)]
		|	(lit("check-sat") > ")")[px::bind(&SMTLIBParser::check, px::ref(*this))]
		|	(lit("declare-const") > symbol > domain > ")")[px::bind(&SMTLIBParser::declareConst, px::ref(*this), qi::_1, qi::_2)]
		|	(lit("declare-fun") > symbol > "(" > symlist > ")" > domain > ")")[px::bind(&SMTLIBParser::declareFun, px::ref(*this), qi::_1, qi::_2, qi::_3)]
		|	(lit("declare-sort") > symbol > integral > ")")[px::bind(&SMTLIBParser::declareSort, px::ref(*this), qi::_1, qi::_2)]
		|	(lit("define-fun") > symbol > "(" > symlist > ")" > domain > formula > ")")[px::bind(&SMTLIBParser::defineFun, px::ref(*this), qi::_1, qi::_2, qi::_3, qi::_4)]
		|	(lit("define-sort") > symbol > "(" > symlist > ")" > symbol > ")")[px::bind(&SMTLIBParser::defineSort, px::ref(*this), qi::_1, qi::_2, qi::_3)]
		|	(lit("exit") > ")")[px::bind(&SMTLIBParser::exit, px::ref(*this))]
		|	(lit("get-assertions") > ")")[px::bind(&SMTLIBParser::getAssertions, px::ref(*this))]
		|	(lit("get-assignment") > ")")[px::bind(&SMTLIBParser::getAssignment, px::ref(*this))]
		|	(lit("get-info") > key > ")")[px::bind(&SMTLIBParser::getInfo, px::ref(*this), qi::_1)]
		|	(lit("get-option") > key > ")")[px::bind(&SMTLIBParser::getOption, px::ref(*this), qi::_1)]
		|	(lit("get-proof") > ")")[px::bind(&SMTLIBParser::getProof, px::ref(*this))]
		|	(lit("get-unsat-core") > ")")[px::bind(&SMTLIBParser::getUnsatCore, px::ref(*this))]
		|	(lit("get-value") > varlist > ")")[px::bind(&SMTLIBParser::getValue, px::ref(*this), qi::_1)]
		|	(lit("pop") > integral > ")")[px::bind(&SMTLIBParser::pop, px::ref(*this), qi::_1)]
		|	(lit("push") > integral > ")")[px::bind(&SMTLIBParser::push, px::ref(*this), qi::_1)]
		|	(lit("set-info") > key > value > ")")[px::bind(&SMTLIBParser::setInfo, px::ref(*this), qi::_1, qi::_2)]
		|	(lit("set-logic") > logic > ")")[px::bind(&SMTLIBParser::setLogic, px::ref(*this), qi::_1)]
		|	(lit("set-option") > key > value > ")")[px::bind(&SMTLIBParser::setOption, px::ref(*this), qi::_1, qi::_2)]
	);
	cmd.name("command");

	formula = 
			(bind_bool >> boundary)[_val = qi::_1]
		|	(var_bool >> boundary)[_val = px::bind(&SMTLIBParser::mkBoolean, px::ref(*this), qi::_1)]
		|	lit("true")[_val = px::bind(&trueFormula)]
		|	lit("false")[_val = px::bind(&falseFormula)]
		|	("(" >> formula_op >> ")")[_val = qi::_1]
	;
	formula.name("formula");
	
	formula_op =
				((op_bool >> +formula)[_val = px::bind(&SMTLIBParser::mkFormula, px::ref(*this), qi::_1, qi::_2)])
			|	(relation >> polynomial >> polynomial)[_val = px::bind(&SMTLIBParser::mkConstraint, px::ref(*this), qi::_2, qi::_3, qi::_1)]
			|	(lit("as")[qi::_pass = false] > symbol > symbol)
			|	(lit("not") > formula[_val = px::bind(&newNegation, qi::_1)])
			|	((lit("implies") | "=>") >> formula >> formula)[_val = px::bind(newImplication, qi::_1, qi::_2)]
			|	(lit("let")[px::bind(&SMTLIBParser::pushVariableStack, px::ref(*this))]
				> ("(" > bindlist > ")" > formula)[px::bind(&SMTLIBParser::popVariableStack, px::ref(*this)), _val = qi::_1])
			|	("exists" > bindlist > formula)
			|	("forall" > bindlist > formula)
			|	("ite" > (formula > formula > formula)[_val = px::bind(&SMTLIBParser::mkIteInFormula, px::ref(*this), qi::_1, qi::_2, qi::_3)])
			|	(("!" > formula > *attribute)[px::bind(&Formula::annotate, qi::_1, qi::_2), _val = qi::_1])
	;
	formula_op.name("formula operation");

	polynomial_op = op_theory >> +polynomial;
	polynomial_op.name("polynomial operation");
	polynomial_ite = lit("ite") > (formula > polynomial > polynomial)[_val = px::construct<Polynomial>(px::bind(&SMTLIBParser::mkIteInExpr, px::ref(*this), qi::_1, qi::_2, qi::_3))];
	polynomial_ite.name("polynomial if-then-else");
	polynomial =
			(bind_theory >> boundary)
		|	(var_theory >> boundary)
		|	decimal
		|	integral
		|	("(" >> (
				polynomial_ite
			|	polynomial_op
		) >> ")")
	;
	polynomial.name("polynomial");

	main = *cmd > qi::eoi;
	main.name("SMTLib File");

	qi::on_error<qi::fail>(main, errorHandler(px::ref(*this), qi::_1, qi::_2, qi::_3, qi::_4));
/*
	qi::on_success(bindlist, successHandler(px::ref(*this), px::ref(bindlist), qi::_val, qi::_1, qi::_2));
	qi::on_success(polynomial, successHandler(px::ref(*this), px::ref(polynomial), qi::_val, qi::_1, qi::_2));
	qi::on_success(polynomial_op, successHandler(px::ref(*this), px::ref(polynomial_op), qi::_val, qi::_1, qi::_2));
	qi::on_success(formula, successHandlerPtr(px::ref(*this), px::ref(formula), qi::_val, qi::_1, qi::_2));
	qi::on_success(formula_op, successHandlerPtr(px::ref(*this), px::ref(formula_op), qi::_val, qi::_1, qi::_2));
	qi::on_success(cmd, successHandler(px::ref(*this), px::ref(cmd), qi::_val, qi::_1, qi::_2));
	qi::on_success(main, successHandler(px::ref(*this), px::ref(main), qi::_val, qi::_1, qi::_2));
*/
}

bool SMTLIBParser::parse(std::istream& in, const std::string& filename) {
	in.unsetf(std::ios::skipws);
	mInputStream = &in;
	BaseIteratorType basebegin(in);
	Iterator begin(basebegin);
	Iterator end;
	Skipper skipper;
	try {
		bool result = qi::phrase_parse(begin, end, main, skipper);
		std::cout << "Result: " << result << std::endl;
		return result;
	} catch (const qi::expectation_failure<PositionIteratorType>& e) {
		// If the parser expected content different than the one provided, display information about the location of the error.
		std::size_t lineNumber = boost::spirit::get_line(e.first);

		// Now propagate exception.
		std::cerr << "Catched an expectation failure" << std::endl;
		std::cerr << "Parsing error in line " << lineNumber << std::endl;
		std::cerr << "expected " << e.what_ << std::endl;
		std::cerr << "but got '" << std::string(e.first, e.last) << "'" << std::endl;
		return false;
	} catch (const std::runtime_error& e) {
		std::cerr << "error: " << e.what() << std::endl;
		return false;
	} catch (...) {
		std::cerr << "catched something" << std::endl;
		return false;
	}
}

smtrat::Polynomial* SMTLIBParser::mkPolynomial(const TheoryOperation& op, std::vector<Polynomial*>& v) {
	assert(!v.empty());
	Polynomial* res = v.front();
	if ((op == SUB) && (v.size() == 1)) {
		// special treatment of unary minus.
		(*res) *= -1;
		return res;
	}
	// all other operators shall have at least two arguments.
	assert(v.size() >= 2);
	for (unsigned i = 1; i < v.size(); i++) {
		switch (op) {
			case ADD: (*res) += (*v[i]); break;
			case SUB: (*res) -= (*v[i]); break;
			case MUL: (*res) *= (*v[i]); break;
			case DIV: 
				assert(v[i]->isConstant());
				(*res) /= v[i]->constantPart();
				break;
		}
		delete v[i];
	}
	return res;
}

}
}
