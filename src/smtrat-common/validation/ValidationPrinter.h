#pragma once

#include "ValidationPoint.h"
#include "ValidationCollector.h"
#include <carl-io/SMTLIBStream.h>

#include <fstream>
#include <iostream>
#include <iomanip>

namespace smtrat {
namespace validation {

enum class ValidationOutputFormat {
	SMTLIB
};

template<ValidationOutputFormat SOF>
struct ValidationPrinter {};

template<ValidationOutputFormat SOF>
std::ostream& operator<<(std::ostream& os, ValidationPrinter<SOF>);

template<>
std::ostream& operator<<(std::ostream& os, ValidationPrinter<ValidationOutputFormat::SMTLIB>) {
	carl::SMTLIBStream sls;
	sls.setInfo("smt-lib-version", "2.0");
	for (const auto& s: ValidationCollector::getInstance().points()) {
		if (s->formulas().empty()) continue;
		for (const auto& kv: s->formulas()) {
			sls.reset();
			sls.declare(/* TODO logic */);
			sls.setOption("interactive-mode", "true");
			sls.setInfo("status", (kv.second ? "sat" : "unsat"));
			carl::carlVariables vars = carl::variables(kv.first);
			// TODO comment on which instance etc
			// sls << "(declare-fun " << _label << " () " << "Bool" << ")\n";
			sls.declare(vars);
			sls.assertFormula(kv.first);
			sls.getAssertions();
			sls.checkSat();
		}
	}
	sls.exit();
	os << sls.str();
	return os;
}

auto validation_formulas_as_smtlib() {
	return ValidationPrinter<ValidationOutputFormat::SMTLIB>();
}

void validation_formulas_to_smtlib_file(const std::string& filename) { // Settings().validation.log_filename
	std::ofstream file;
	file.open(filename, std::ios::out);
	file << validation_formulas_as_smtlib();
	file.close();
}


}
}