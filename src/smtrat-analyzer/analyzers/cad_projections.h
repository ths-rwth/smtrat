#pragma once

#include "../statistics.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat::analyzer {

void analyze_cad_projections(const FormulaT& f, AnalyzerStatistics& stats);

}