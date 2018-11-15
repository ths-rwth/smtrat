#pragma once

#include "../../Common.h"

#include "cad/qe.h"

namespace smtrat {
namespace qe {

FormulaT eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers) {
	return cad::eliminateQuantifiers(qfree, quantifiers);
}

}
}