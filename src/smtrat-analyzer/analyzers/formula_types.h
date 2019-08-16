#pragma once

#include "../statistics.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat::analyzer {

void analyze_formula_types(const FormulaT& f, AnalyzerStatistics& stats);

}