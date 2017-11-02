#include "ParserWrapper.h"

#include "Parser.h"

namespace smtrat {
	bool parseSMT2File(parser::InstructionHandler* handler, bool queueInstructions, std::istream& input) {
		parser::SMTLIBParser parser(handler, queueInstructions);
		return parser.parse(input);
	}
}
