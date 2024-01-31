#include "formula_types.h"

#include "utils.h"
#include <carl-formula/formula/functions/CNF.h>


namespace smtrat::analyzer {

void analyze_cnf(const FormulaT& f, AnalyzerStatistics& stats) {
	FormulaT cnf = carl::to_cnf(f, false);

	std::size_t num_clauses = 0;
	std::size_t max_clause_size = 0;
	std::size_t min_clause_size = 0;
	std::size_t sum_clause_size = 0;

	if (cnf.is_atom() || (cnf.type() == carl::FormulaType::OR)) {
		num_clauses = 1;
		max_clause_size = cnf.size(); // size is 1 for atoms
		min_clause_size = cnf.size();
		sum_clause_size = cnf.size();
	} else {
		assert(cnf.type() == carl::FormulaType::AND);
		num_clauses = cnf.size();
		for (const auto& sub: cnf) {
			sum_clause_size += sub.size();
			if (sub.size() > max_clause_size) max_clause_size = sub.size();
			if (sub.size() < min_clause_size || min_clause_size == 0) min_clause_size = sub.size();
		}
	}

	stats.add("num_clauses", num_clauses);
	stats.add("max_clause_size", max_clause_size);
	stats.add("min_clause_size", min_clause_size);
	stats.add("sum_clause_size", sum_clause_size);
	stats.add("avg_clause_size", static_cast<float>(sum_clause_size)/static_cast<float>(num_clauses));
}

}