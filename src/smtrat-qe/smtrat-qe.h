#pragma once

#include <smtrat-common/smtrat-common.h>

#include "QEQuery.h"

//#include "cad/qe.h"
#include "fm/qe.h"
#include "fmplex/qe.h"

namespace smtrat::qe {

// namespace elimination_method = fm;
namespace elimination_method = fmplex;

inline void qe(const FormulaT& formula, std::ostream& output){
	auto res = elimination_method::qe(formula);
	output << "Equivalent Quantifier-Free Formula: " << res << std::endl;
}


inline void eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers, std::ostream& output) {
	if (qfree.is_real_constraint_conjunction()) {
		const FormulasT& subfs = qfree.subformulas();
		if (std::all_of(
			subfs.begin(), subfs.end(),
			[](const auto& c){
		    	return (c.type() == carl::FormulaType::CONSTRAINT) && (c.constraint().lhs().is_linear());
			}
		)) {
			SMTRAT_LOG_DEBUG("smtrat.qe","call fmplex");
			FormulaT res = elimination_method::eliminateQuantifiers(qfree, quantifiers);
			output << "Equivalent Quantifier-Free Formula: " << res << std::endl;
		}
	} else {
		SMTRAT_LOG_DEBUG("smtrat.qe","call cad");
		//return cad::eliminateQuantifiers(qfree, quantifiers);
		assert(false);
	}
}

}