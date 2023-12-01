#pragma once

#include <smtrat-common/smtrat-common.h>

#include "QEQuery.h"

//#include "cad/qe.h"
//#include "fm/qe.h"
#include "coverings/qe.h"

namespace smtrat::qe {

inline std::optional<FormulaT> qe(const FormulaT& formula){
	return coverings::qe(formula);
}


} // namespace smtrat::qe