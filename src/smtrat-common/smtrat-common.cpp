#include "smtrat-common.h"

#ifdef EXTERNALIZE_CLASSES
namespace carl {

template class MultivariatePolynomial<smtrat::Rational>;
template class Constraint<smtrat::Poly>;
template class Formula<smtrat::Poly>;

}
#endif
