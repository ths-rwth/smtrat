#include "qe.h"

#include "FourierMotzkinQE.h"

namespace smtrat::qe::fm {

FormulaT eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers) {
	FourierMotzkinQE elim(qfree, quantifiers);
	return elim.eliminateQuantifiers();
}

} // namespace
