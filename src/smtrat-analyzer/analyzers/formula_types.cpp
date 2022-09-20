#include "formula_types.h"

#include "utils.h"

namespace smtrat::analyzer {

void analyze_formula_types(const FormulaT& f, AnalyzerStatistics& stats) {
	std::size_t num_formulas = 0;
	std::size_t num_or = 0;
	std::size_t num_constraints = 0;
	std::size_t num_equalities = 0;
	std::size_t num_disequalities = 0;
	std::size_t num_weak_inequalities = 0;
	std::size_t num_strict_inequalities = 0;
	std::size_t num_variable_occurrences = 0;
	DegreeCollector dc;


	carl::visit(f, [&](const FormulaT& f){
		++num_formulas;
		if (f.type() == carl::FormulaType::OR) {
			++num_or;
		} else if (f.type() == carl::FormulaType::CONSTRAINT) {
			++num_constraints;
			num_variable_occurrences += f.variables().size();
			dc(f.constraint());
			switch (f.constraint().relation()) {
				case carl::Relation::LESS: ++num_strict_inequalities; break;
				case carl::Relation::LEQ: ++num_weak_inequalities; break;
				case carl::Relation::EQ: ++num_equalities; break;
				case carl::Relation::NEQ: ++num_equalities; break;
				case carl::Relation::GEQ: ++num_weak_inequalities; break;
				case carl::Relation::GREATER: ++num_strict_inequalities; break;
			}
		}
	});

	stats.add("num_formulas", num_formulas);
	stats.add("num_or", num_or);
	stats.add("num_constraints", num_constraints);
	stats.add("num_equalities", num_equalities);
	stats.add("num_disequalities", num_disequalities);
	stats.add("num_weak_inequalities", num_weak_inequalities);
	stats.add("num_strict_inequalities", num_strict_inequalities);

	stats.add("num_variable_occurrences", num_variable_occurrences);

	stats.add("constraint_deg_max", dc.degree_max);
	stats.add("constraint_deg_sum", dc.degree_sum);
}

}