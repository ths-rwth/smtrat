#include "FunctionArgumentParser.h"

#ifdef __VS
#pragma warning(push, 0)
#include <boost/fusion/include/std_pair.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#pragma warning(pop)
#else
#include <boost/fusion/include/std_pair.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#endif

#include "FormulaParser.h"
#include "BitvectorParser.h"
#include "PolynomialParser.h"
#include "UninterpretedParser.h"

namespace smtrat {
namespace parser {

FunctionArgumentParser::FunctionArgumentParser(FormulaParser* formulaPtr, BitvectorParser* bitvectorPtr, UninterpretedParser* uninterpretedPtr, PolynomialParser* polynomialPtr):
	FunctionArgumentParser::base_type(main, "argument")
{
	main = *formulaPtr | *bitvectorPtr | *uninterpretedPtr | *polynomialPtr;
}

}
}
