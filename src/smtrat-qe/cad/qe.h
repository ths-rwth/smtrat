#pragma once

#include <lib/Common.h>

namespace smtrat::qe::cad {

FormulaT eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers);

}