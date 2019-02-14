#pragma once

#include <smtrat-common/smtrat-common.h>

#include <string>

namespace smtrat {

/**
 * Loads the smt2 file specified in filename and returns the formula.
 * This function ignores most SMT-LIB commands but simply accumulated all asserted formulas.
 */
FormulaT parse_formula(const std::string& filename);

int analyze_file(const std::string& filename);

}