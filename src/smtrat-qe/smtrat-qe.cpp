#include "smtrat-qe.h"

//#include "cad/qe.h"
#include "fm/qe.h"
#include "fmplex/qe.h"
#include "coverings/qe.h"

namespace smtrat::qe {

std::optional<FormulaT> qe(const FormulaT& formula) {
	std::string qe_method = settings_module().get("qe-method", std::string("covering"));
	if (qe_method == "covering") return coverings::qe(formula);
	if (qe_method == "fmplex") return fmplex::qe(formula);
	if (qe_method == "fm") return fm::qe(formula);

	SMTRAT_LOG_WARN("smtrat.qe", "Unknown qe-method " << qe_method << ".");
	SMTRAT_LOG_WARN("smtrat.qe", "Defaulting to covering.");
	return coverings::qe(formula);
}

}