#include "smtrat-analyzer.h"

#include "analyzers/cad_projections.h"
#include "analyzers/formula_types.h"
#include "analyzers/variables.h"

namespace smtrat {

analyzer::AnalyzerStatistics& analyze_formula(const FormulaT& f) {
	analyzer::AnalyzerStatistics& stats = statistics_get<analyzer::AnalyzerStatistics>("analyzer");

	analyzer::analyze_variables(f, stats);
	analyzer::analyze_formula_types(f, stats);
	analyzer::analyze_cad_projections(f, stats);

	return stats;
}

}