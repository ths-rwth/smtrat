#pragma once

#include "InstructionHandler.h"

namespace smtrat {

bool parseSMT2File(parser::InstructionHandler& handler, bool queueInstructions, std::istream& input);
	
}
