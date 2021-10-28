#pragma once

#include "config.h"
#include "types.h"
#include "logging.h"
#include "settings/Settings.h"
#include "validation/Validation.h"
#include "checkpoints/Checkpoints.h"


#ifdef EXTERNALIZE_CLASSES
namespace carl {

extern template class MultivariatePolynomial<smtrat::Rational>;
extern template class Constraint<smtrat::Poly>;
extern template class Formula<smtrat::Poly>;

}
#endif
