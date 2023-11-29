#include "qe.h"

#include "FourierMotzkinQE.h"
#include "../fmplex/FMplexQEStatistics.h"

namespace smtrat::qe::fm {

FormulaT qe(const FormulaT& f) {
	SMTRAT_TIME_START(t);
	 // TODO: make sure more general inputs can be handled
	assert(f.type() == carl::FormulaType::EXISTS);
	QEQuery q = {{QuantifierType::EXISTS, f.quantified_variables()}};
	FourierMotzkinQE elim(f.quantified_formula(), q);
	FormulaT result = elim.eliminateQuantifiers();
	SMTRAT_TIME_FINISH(FMplexQEStatistics::get_instance().timer(), t);
	SMTRAT_STATISTICS_CALL(
		FMplexQEStatistics::get_instance().output(result.is_nary() ? result.subformulas().size() : 1)
	);
	return result;
}

FormulaT eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers) {
	FourierMotzkinQE elim(qfree, quantifiers);
	return elim.eliminateQuantifiers();
}

} // namespace
