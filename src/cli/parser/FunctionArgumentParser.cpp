#include "FunctionArgumentParser.h"

#include <boost/fusion/include/std_pair.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>

#include "../../lib/Common.h"
#include "FormulaParser.h"
#include "PolynomialParser.h"
#include "UninterpretedParser.h"

namespace smtrat {
namespace parser {

FunctionArgumentParser::FunctionArgumentParser(FormulaParser* formulaPtr, UninterpretedParser* uninterpretedPtr, PolynomialParser* polynomialPtr):
	FunctionArgumentParser::base_type(main, "argument"), 
	formula(formulaPtr),
	uninterpreted(uninterpretedPtr),
	polynomial(polynomialPtr)
{
	main = *formulaPtr | *uninterpretedPtr | *polynomialPtr;
}

}
}