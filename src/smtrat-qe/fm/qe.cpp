#include "qe.h"

#include "FourierMotzkinQE.h"
#include "FMQEStatistics.h"

namespace smtrat::qe::fm {

std::optional<FormulaT> qe(const FormulaT& f) {
	SMTRAT_TIME_START(t);
	// TODO: make sure more general inputs can be handled
	if (f.type() != carl::FormulaType::EXISTS) return std::nullopt;
	if (!f.quantified_formula().is_real_constraint_conjunction() 
		&& f.quantified_formula().type() != carl::FormulaType::CONSTRAINT)  return std::nullopt;

	// TODO: get rid of QEQuery
	QEQuery q = {{QuantifierType::EXISTS, f.quantified_variables()}};
	FourierMotzkinQE elim(f.quantified_formula(), q);
	FormulaT result = elim.eliminateQuantifiers();
	SMTRAT_TIME_FINISH(FMQEStatistics::get_instance().timer(), t);
	SMTRAT_STATISTICS_CALL(
		FMQEStatistics::get_instance().output(result.is_nary() ? result.subformulas().size() : 1)
	);
	return result;
}

} // namespace
