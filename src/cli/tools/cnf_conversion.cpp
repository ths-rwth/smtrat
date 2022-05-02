#include "cnf_conversion.h"

#include "config.h"
#include <smtrat-common/smtrat-common.h>

#ifdef CLI_ENABLE_CNF_CONVERSION

#include "parser_smtlib_utils.h"
#include "execute_smtlib.h"

#include <carl-formula/formula/functions/to_cnf.h>
#include <carl-io/DIMACSExporter.h>
#include <carl-io/SMTLIBStream.h>

namespace smtrat {

int convert_to_cnf_dimacs(const std::string& filename, const std::string& outfile) {
	auto e = parseformula::FormulaCollector();
	executeFile(filename, e);

	carl::DIMACSExporter<Poly> exporter;
	exporter(carl::to_cnf(e.getFormula()));

	if (outfile.empty()) {
		e.regular() << exporter;
	} else {
		std::ofstream file(outfile);
		file << exporter;
		file.close();
	}

	return 0;
}

int convert_to_cnf_smtlib(const std::string& filename, const std::string& outfile) {
	auto e = parseformula::FormulaCollector();
	executeFile(filename, e);

	auto f_in_cnf = carl::to_cnf(e.getFormula());

	if (outfile.empty()) {
		e.regular() << carl::outputSMTLIB(e.getLogic(), { f_in_cnf });
	} else {
		std::ofstream file(outfile);
		file << carl::outputSMTLIB(e.getLogic(), { f_in_cnf });
		file.close();
	}

	return 0;
}

}

#else

namespace smtrat {

int convert_to_cnf_dimacs(const std::string&, const std::string&) {
	SMTRAT_LOG_ERROR("smtrat", "This version of SMT-RAT was compiled without support for stand-alone CNF conversion.");
	return 0;
}

int convert_to_cnf_smtlib(const std::string&, const std::string&) {
	SMTRAT_LOG_ERROR("smtrat", "This version of SMT-RAT was compiled without support for stand-alone CNF conversion.");
	return 0;
}

}

#endif