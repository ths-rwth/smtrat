#pragma once

#include "../QEQuery.h"
#include <smtrat-common/smtrat-common.h>

namespace smtrat::qe::fmplex {

FormulaT qe(const FormulaT& f);
FormulaT eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers);

}
