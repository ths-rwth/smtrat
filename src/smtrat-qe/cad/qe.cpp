#include "qe.h"

#include "CADElimination.h"

namespace smtrat::qe::cad {

FormulaT eliminateQuantifiers(const FormulaT& qfree, const QEQuery& quantifiers) {
	cad::CADElimination elim(qfree, quantifiers);
	return elim.eliminateQuantifiers();
}

}