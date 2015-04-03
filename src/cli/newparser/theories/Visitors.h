#pragma once

#include "../Common.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {
namespace visitors {

struct BindVisitor {
	ParserState* state;
	std::string symbol;
};

}
}
}
