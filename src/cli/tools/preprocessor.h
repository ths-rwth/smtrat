#pragma once

#include <string>

namespace smtrat {

/**
 * Loads the smt2 file specified in filename and runs the preprocessing strategy.
 * The resulting (simplified) problem is written to outfile (or stdout if outfile is empty).
 */
int preprocess_file(const std::string& filename, const std::string& outfile);

}