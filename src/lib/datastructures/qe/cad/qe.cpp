#include "qe.h"

#include "QE.h"

namespace smtrat::qe::cad {

FormulaT eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers) {
	cad::QE qe(qfree, quantifiers);
	return qe.eliminateQuantifiers();
}

}