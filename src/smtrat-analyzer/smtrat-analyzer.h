#pragma once

#include <smtrat-common/smtrat-common.h>
#include "analyzer_settings.h"
#include "analyzer_statistics.h"

namespace smtrat {

analyzer::AnalyzerStatistics& analyze_formula(const FormulaT& f);

}