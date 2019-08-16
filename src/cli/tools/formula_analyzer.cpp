#include "formula_analyzer.h"

#include "config.h"
#include <smtrat-common/smtrat-common.h>

#ifdef CLI_ENABLE_ANALYZER

#include "parser_smtlib_utils.h"
#include "execute_smtlib.h"

namespace smtrat {

int analyze_file(const std::string& filename) {
	auto e = parseformula::FormulaCollector();
	executeFile(filename, e);

	auto& stats = analyze_formula(e.getFormula());

	if (e.has_info("status")) {
		stats.add("answer", e.get_info("status"));
	}

	return 0;
}

}

#else

namespace smtrat {

int analyze_file(const std::string& filename) {
	return 0;
}

}

#endif