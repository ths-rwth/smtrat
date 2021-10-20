#pragma once

#include "config.h"
#include "logging.h"
#include "settings/Settings.h"
#include "types.h"
#ifdef SMTRAT_DEVOPTION_Validation
#include "validation/Validation.h"
#endif



#ifdef EXTERNALIZE_CLASSES
namespace carl {

extern template class MultivariatePolynomial<smtrat::Rational>;
extern template class Constraint<smtrat::Poly>;
extern template class Formula<smtrat::Poly>;

}
#endif
