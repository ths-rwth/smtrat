#pragma once

#include <string>

namespace smtrat {

int convert_to_cnf_dimacs(const std::string& filename, const std::string& outfile);
int convert_to_cnf_smtlib(const std::string& filename, const std::string& outfile);

}