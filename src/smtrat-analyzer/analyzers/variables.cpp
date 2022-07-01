#include "variables.h"

namespace smtrat::analyzer {

void analyze_variables(const FormulaT& f, AnalyzerStatistics& stats) {
	carl::carlVariables vars;
	carl::variables(f,vars);

	stats.add("num_variables", vars.size());
	stats.add("num_variables_boolean", vars.boolean().size());
	stats.add("num_variables_theory", vars.integer().size() + vars.real().size() + vars.bitvector().size() + vars.uninterpreted().size());
	stats.add("num_variables_arithmetic_real", vars.real().size());
	stats.add("num_variables_arithmetic_int", vars.integer().size());
	stats.add("num_variables_arithmetic", vars.integer().size() + vars.real().size());
	stats.add("num_variables_bitvector", vars.bitvector().size());
	stats.add("num_variables_uninterpreted", vars.uninterpreted().size());
}

}