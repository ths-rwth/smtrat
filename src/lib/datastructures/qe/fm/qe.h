#pragma once

#include "../../../Common.h"

namespace smtrat::qe::fm {

FormulaT eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers);

}
