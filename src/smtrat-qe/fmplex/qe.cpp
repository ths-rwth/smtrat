#include "qe.h"
#include "FMplexQE.h"
#include "FMplexQEStatistics.h"

namespace smtrat::qe::fmplex {

std::optional<FormulaT> qe(const FormulaT& f) {
	SMTRAT_TIME_START(t);
	// TODO: make sure more general inputs can be handled
	if (f.type() != carl::FormulaType::EXISTS) return std::nullopt;
	if (!f.quantified_formula().is_real_constraint_conjunction() 
		&& f.quantified_formula().type() != carl::FormulaType::CONSTRAINT)  return std::nullopt;

	// TODO: get rid of QEQuery
	QEQuery q = {{QuantifierType::EXISTS, f.quantified_variables()}};
	FMplexQE elim(f.quantified_formula(), q);
	FormulaT result = elim.eliminate_quantifiers();
	SMTRAT_TIME_FINISH(FMplexQEStatistics::get_instance().timer(), t);
	SMTRAT_VALIDATION_ADD("smtrat.qe.fmplex","output", result, true);
	SMTRAT_STATISTICS_CALL(
		FMplexQEStatistics::get_instance().output(result.is_nary() ? result.subformulas().size() : 1)
	);
	return result;
}

}
