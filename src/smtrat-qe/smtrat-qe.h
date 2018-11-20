#pragma once

#include <smtrat-common/smtrat-common.h>

#include "QEQuery.h"

#include "cad/qe.h"
#include "fm/qe.h"

namespace smtrat {
namespace qe {

inline FormulaT eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers) {
	return cad::eliminateQuantifiers(qfree, quantifiers);
}

}
}