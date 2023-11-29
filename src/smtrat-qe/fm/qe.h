#pragma once

#include "../QEQuery.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat::qe::fm {

FormulaT qe(const FormulaT& f);
FormulaT eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers);

}
