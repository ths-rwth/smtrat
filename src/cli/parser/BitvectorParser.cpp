#include "UninterpretedParser.h"

#include <boost/spirit/include/phoenix_bind.hpp>

namespace smtrat {
namespace parser {

BitvectorParser::BitvectorParser(ParserState* _state):
	BitvectorParser::base_type(bitvector, "bitvector"),
	state(_state)
{
	bitvector = (
			state->var_bitvector[qi::_val = qi::_1]
	);
}

}
}