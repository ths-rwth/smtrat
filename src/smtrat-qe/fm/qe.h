#pragma once

#include "../QEQuery.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat::qe::fm {

std::optional<FormulaT> qe(const FormulaT& f);

}
