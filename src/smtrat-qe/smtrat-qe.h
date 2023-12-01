#pragma once

#include <smtrat-common/smtrat-common.h>

#include "QEQuery.h"

//#include "cad/qe.h"
//#include "fm/qe.h"
#include "coverings/qe.h"

namespace smtrat::qe {

inline void qe(const FormulaT& formula, std::ostream& output){
	auto res = coverings::qe(formula);
	output << "Equivalent Quantifier-Free Formula: " << res << std::endl;
}

inline void eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers, std::ostream& output) {
	auto res = coverings::eliminateQuantifiers(qfree, quantifiers);
	output << "Equivalent Quantifier-Free Formula: " << res << std::endl;

}

} // namespace smtrat::qe