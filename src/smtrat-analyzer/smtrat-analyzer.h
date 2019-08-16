#pragma once

#include "settings.h"
#include "statistics.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat {

analyzer::AnalyzerStatistics& analyze_formula(const FormulaT& f);

}