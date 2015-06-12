#include "UninterpretedParser.h"

#include <boost/spirit/include/phoenix_bind.hpp>

namespace smtrat {
namespace parser {

UninterpretedParser::UninterpretedParser(ParserState* _state, FormulaParser* formula, BitvectorParser* bitvector):
	UninterpretedParser::base_type(uninterpreted, "uninterpreted"),
	state(_state),
	polynomial(_state, formula, this),
	fun_argument(formula, bitvector, this, &polynomial)
{
	uninterpreted = (
			state->var_uninterpreted[qi::_val = qi::_1]
		|	state->bind_uninterpreted[qi::_val = qi::_1]
		|	(qi::lit("(") >> state->funmap_uf >> *fun_argument >> qi::lit(")"))[qi::_val = px::bind(&ParserState::applyUninterpretedFunction, px::ref(state), qi::_1, qi::_2)]
	);
}

}
}