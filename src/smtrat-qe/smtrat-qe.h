#pragma once

#include <smtrat-common/smtrat-common.h>

#include "QEQuery.h"

#include "cad/qe.h"
#include "fm/qe.h"
#include "fmplex/qe.h"

namespace smtrat {
namespace qe {

inline FormulaT eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers) {
	if (qfree.is_real_constraint_conjunction()) {
		const FormulasT& subfs = qfree.subformulas();
		if (std::all_of(
			subfs.begin(), subfs.end(),
			[](const auto& c){
		    	return (c.type() == carl::FormulaType::CONSTRAINT) && (c.constraint().lhs().is_linear());
			}
		)) {
			SMTRAT_LOG_DEBUG("smtrat.qe","call fmplex");
			return fmplex::eliminateQuantifiers(qfree, quantifiers);
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.qe","call cad");
	return cad::eliminateQuantifiers(qfree, quantifiers);
}

}
}