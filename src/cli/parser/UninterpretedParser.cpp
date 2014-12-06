#include "UninterpretedParser.h"

#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_object.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>

namespace smtrat {
namespace parser {

UninterpretedParser::UninterpretedParser(ParserState* state, FormulaParser* formula):
	UninterpretedParser::base_type(uninterpreted, "uninterpreted"),
	polynomial(state, formula, this),
	fun_argument(formula, this, &polynomial),
	state(state)
{
	uninterpreted = (
			state->var_uninterpreted[qi::_val = qi::_1]
		|	state->bind_uninterpreted[qi::_val = qi::_1]
		|	(qi::lit("(") >> state->funmap_uf >> *fun_argument >> qi::lit(")"))[qi::_val = px::bind(&ParserState::applyUninterpretedFunction, px::ref(state), qi::_1, qi::_2)]
	);
}

}
}