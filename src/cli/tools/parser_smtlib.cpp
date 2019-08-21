#include "parser_smtlib.h"

#include "config.h"
#include <smtrat-common/smtrat-common.h>

#ifdef CLI_ENABLE_FORMULAPARSER

#include "execute_smtlib.h"
#include "parser_smtlib_utils.h"

namespace smtrat {

FormulaT parse_smtlib(const std::string& filename) {
	auto e = parseformula::FormulaCollector();
	executeFile(filename, e);
	return e.getFormula();
}

}

#else

namespace smtrat {

FormulaT parse_smtlib(const std::string&) {
	SMTRAT_LOG_ERROR("smtrat", "This version of SMT-RAT was compiled without support for stand-alone formula parsing.");
	return FormulaT();
}

}

#endif