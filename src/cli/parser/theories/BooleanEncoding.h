#pragma once

#include "Common.h"
#include "AbstractTheory.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {

/**
 * Implements the theory of bitvectors.
 */
struct BooleanEncodingTheory: public AbstractTheory  {	
	BooleanEncodingTheory(ParserState* state);
};
	
}
}
