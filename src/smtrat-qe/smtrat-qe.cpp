#include "smtrat-qe.h"

//#include "cad/qe.h"
//#include "fm/qe.h"
#include "coverings/qe.h"

namespace smtrat::qe {

std::optional<FormulaT> qe(const FormulaT& formula) {
	return coverings::qe(formula);
}

}