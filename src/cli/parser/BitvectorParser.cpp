#include "UninterpretedParser.h"

#include <boost/spirit/include/phoenix_bind.hpp>

namespace smtrat {
namespace parser {

BitvectorParser::BitvectorParser(ParserState* _state):
	BitvectorParser::base_type(bitvector, "bitvector"),
	state(_state)
{
	bitvector = (
			state->var_bitvector[qi::_val = px::bind(&BitvectorParser::createVariable, px::ref(*this), qi::_1)]
		|	(buop >> bitvector)[qi::_val = px::bind(&BitvectorParser::createUnary, px::ref(*this), qi::_1, qi::_2)]
		|	(bbop >> bitvector >> bitvector)[qi::_val = px::bind(&BitvectorParser::createBinary, px::ref(*this), qi::_1, qi::_2, qi::_3)]
	);
}

}
}
