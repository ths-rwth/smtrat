#include "Parser.h"

namespace smtrat {
namespace parser {

SMTLIBParser::SMTLIBParser(InstructionHandler* ih) : SMTLIBParser::base_type(main), handler(ih) {

	integral = ("#b" > qi::bin) | qi::uint_ | ("#x" > qi::hex);
	integral.name("integral number");

	var %= var_bool | var_theory;
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
			polynomial[_val = px::bind(&Driver::addTheoryBinding, px::ref(d), qi::_a, qi::_1)]
		|	formula[_val = px::bind(&Driver::booleanBinding, px::ref(d), qi::_a, qi::_1)]
	)[_val = qi::_1];
	binding.name("binding");
	
	cmd = "(" > (
			(lit("assert") > formula[px::bind(&SMTLIBParser::add, px::ref(*this), qi::_1)])
		|	(lit("check-sat")[px::bind(&SMTLIBParser::check, px::ref(*this))])
		|	(lit("declare-const") > (symbol > symbol)[px::bind(&InstructionHandler::declareConst, handler, qi::_1, qi::_2)])
		|	(lit("declare-fun") > (symbol > "(" > symlist > ")" > symbol)[px::bind(&SMTLIBParser::declareFun, px::ref(*this), qi::_1, qi::_2, qi::_3)])
		|	(lit("declare-sort") > (symbol > integral)[px::bind(&InstructionHandler::declareSort, handler, qi::_1, qi::_2)])
		|	(lit("define-fun") > (symbol > "(" > symlist > ")" > symbol > formula)[px::bind(&InstructionHandler::defineFun, handler, qi::_1, qi::_2, qi::_3, qi::_4)])
		|	(lit("define-sort") > (symbol > "(" > symlist > ")" > symbol)[px::bind(&InstructionHandler::defineSort, handler, qi::_1, qi::_2, qi::_3)])
		|	(lit("exit")[px::bind(&InstructionHandler::exit, px::ref(handler))])
		|	(lit("get-assertions")[px::bind(&InstructionHandler::getAssertions, handler)])
		|	(lit("get-assignment")[px::bind(&InstructionHandler::getAssignment, handler)])
		|	(lit("get-info") > key[px::bind(&InstructionHandler::getInfo, handler, qi::_1)])
		|	(lit("get-option") > key[px::bind(&InstructionHandler::getOption, handler, qi::_1)])
		|	(lit("get-proof")[px::bind(&InstructionHandler::getProof, handler)])
		|	(lit("get-unsat-core")[px::bind(&InstructionHandler::getUnsatCore, handler)])
		|	(lit("get-value") > varlist[px::bind(&InstructionHandler::getValue, handler, qi::_1)])
		|	(lit("pop") > integral[px::bind(&InstructionHandler::pop, handler, qi::_1)])
		|	(lit("push") > integral[px::bind(&InstructionHandler::push, handler, qi::_1)])
		|	(lit("set-info") > (key > value)[px::bind(&InstructionHandler::setInfo, handler, qi::_1, qi::_2)])
		|	(lit("set-logic") > logic[px::bind(&InstructionHandler::setLogic, handler, qi::_1)])
		|	(lit("set-option") > (key > value)[px::bind(&InstructionHandler::setOption, handler, qi::_1, qi::_2)])
	) > ")";
	cmd.name("command");

	formula = 
			var_bool[_val = px::bind(&Driver::mkBoolean, px::ref(d), qi::_1)]
		|	lit("true")[_val = px::bind(&Driver::mkTrue, px::ref(d))]
		|	lit("false")[_val = px::bind(&Driver::mkFalse, px::ref(d))]
		|	("(" > formula_op[_val = qi::_1] > ")")
	;
	formula.name("formula");
	
	formula_op =
				(lit("=") >> (formula > formula)[px::bind(&Driver::restoreTwoFormulaMode, px::ref(d)), _val = px::bind(&Driver::mkFormula, px::ref(d), px::if_else(px::bind(&Driver::polarity, px::ref(d)),IFF,XOR), qi::_1, qi::_2)])
			|	(relation > polynomial > polynomial)[_val = px::bind(&Driver::mkConstraint, px::ref(d), qi::_2, qi::_3, qi::_1)]
			|	(lit("as")[qi::_pass = false] > symbol > symbol)
			|	(lit("not")[px::bind(&Driver::changePolarity, px::ref(d))] > formula[px::bind(&Driver::changePolarity, px::ref(d)), _val = qi::_1])
			|	formula_implication

			/// @todo make nary
			|	(lit("iff")[px::bind(&Driver::setTwoFormulaMode, px::ref(d), true)] 
				> (formula > formula)[px::bind(&Driver::restoreTwoFormulaMode, px::ref(d)), _val = px::bind(&Driver::mkFormula, px::ref(d), IFF, qi::_1, qi::_2)])
			/// @todo make nary
			|	(lit("xor")[px::bind(&Driver::setTwoFormulaMode, px::ref(d), true)]
				> (formula > formula)[px::bind(&Driver::restoreTwoFormulaMode, px::ref(d)), _val = px::bind(&Driver::mkFormula, px::ref(d), XOR, qi::_1, qi::_2)])
			|	((op_bool > +formula)[_val = px::bind(&Driver::mkFormula, px::ref(d), qi::_1, qi::_2)])
			|	(lit("let")[px::bind(&Driver::pushVariableStack, px::ref(d)), px::bind(&Driver::setTwoFormulaMode, px::ref(d), true)]
				> (bindlist > formula)[_val = px::bind(&Driver::appendBindings, px::ref(d), qi::_1, qi::_2), px::bind(&Driver::popVariableStack, px::ref(d))])
			|	("exists" > bindlist > formula)
			|	("forall" > bindlist > formula)
			|	("ite" > (formula > formula > formula)[_val = px::bind(&Driver::mkIteInFormula, px::ref(d), qi::_1, qi::_2, qi::_3)])
			|	(("!" > formula > *attribute)[px::bind(&Formula::annotate, qi::_1, qi::_2), _val = qi::_1])
	;
	formula_op.name("formula operation");

	formula_implication = (
		(lit("implies") | "=>")[qi::_a = px::if_else(px::bind(&Driver::polarity, px::ref(d)),OR,AND), px::bind(&Driver::changePolarity, px::ref(d))]
		> formula[px::bind(&Driver::changePolarity, px::ref(d))] 
		> formula
		)[_val = px::bind(&Driver::mkFormula, px::ref(d), qi::_a, qi::_1, qi::_2)]
	;	
	formula_implication.name("implication");

	polynomial =
			var_theory[_val = px::bind(&Driver::mkPolynomial, px::ref(d), qi::_1)]
		|	decimal[_val = px::new_<Polynomial>(qi::_1)]
		|	integral[_val = px::new_<Polynomial>(px::construct<Rational>(qi::_1))]
		|	("(" > (
				(lit("ite")[px::bind(&Driver::setPolarity, px::ref(d), true), px::bind(&Driver::setTwoFormulaMode, px::ref(d), true)]
					> (formula > polynomial > polynomial)[_val = px::new_<Polynomial>(px::bind(&Driver::mkIteInExpr, px::ref(d), qi::_1, qi::_2, qi::_3))])
			|	(op_theory > +polynomial)[_val = px::bind(&mkPolynomial, qi::_1, qi::_2)]
		) > ")")
	;
	polynomial.name("polynomial");

	main = *cmd > qi::eoi;
	main.name("SMTLib File");

	qi::on_error<qi::fail>(main, errorHandler(px::ref(*this), qi::_1, qi::_2, qi::_3, qi::_4));

	qi::on_success(polynomial, successHandler(px::ref(*this), px::ref(polynomial), qi::_val));
	qi::on_success(formula, successHandler(px::ref(*this), px::ref(formula), qi::_val));
	qi::on_success(formula_op, successHandler(px::ref(*this), px::ref(formula_op), qi::_val));
	qi::on_success(cmd, successHandler(px::ref(*this), px::ref(cmd), qi::_val));
}

bool SMTLIBParser::parse(std::istream& in, const std::string& filename) {
	in.unsetf(std::ios::skipws);
	BaseIteratorType basebegin(in);
	Iterator begin(basebegin);
	Iterator end;
	Skipper skipper;
	//std::cerr << "Parsing: " << in.rdbuf() << std::endl;
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
