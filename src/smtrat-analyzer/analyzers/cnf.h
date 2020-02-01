#pragma once

#include "../statistics.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat::analyzer {

void analyze_cnf(const FormulaT& f, AnalyzerStatistics& stats);

}