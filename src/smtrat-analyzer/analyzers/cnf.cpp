#include "formula_types.h"

#include "utils.h"
#include <carl/formula/helpers/to_cnf.h>


namespace smtrat::analyzer {

void analyze_cnf(const FormulaT& f, AnalyzerStatistics& stats) {
	FormulaT cnf = carl::to_cnf(f, false);

	std::size_t num_clauses = cnf.size();
	std::size_t max_clause_size = 0;
	std::size_t min_clause_size = 0;
	std::size_t sum_clause_size = 0;

	for (const auto& sub: cnf) {
		sum_clause_size += sub.size();
		if (sub.size() > max_clause_size) max_clause_size = sub.size();
		if (sub.size() < min_clause_size || min_clause_size == 0) min_clause_size = sub.size();
	}

	stats.add("num_clauses", num_clauses);
	stats.add("max_clause_size", max_clause_size);
	stats.add("min_clause_size", min_clause_size);
	stats.add("sum_clause_size", sum_clause_size);
	stats.add("avg_clause_size", static_cast<float>(sum_clause_size)/static_cast<float>(num_clauses));
}

}