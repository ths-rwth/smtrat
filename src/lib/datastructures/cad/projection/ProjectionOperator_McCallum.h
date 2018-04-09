#pragma once

#include "ProjectionOperator_utils.h"

namespace smtrat {
namespace cad {
namespace projection {

/**
 * Contains the implementation of McCallums projection operator as specified in @cite McCallum1985.
 */
namespace mccallum {

/**
 * Implements the part of McCallums projection operator from @cite McCallum1985 that deals with a single polynomial `p`:
 * \f$ coefficients(p) \cup \{ discriminant(p) \} \f$
 */
template<typename Poly, typename Callback>
void single(const Poly& p, carl::Variable variable, Callback&& cb) {
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "McCallum_single(" << p << ", " << variable << ") -> Collins_single");
	cb(projection::discriminant(variable, p));
	for (const auto& coeff : p.coefficients()) {
		if (coeff.isConstant()) continue;
		SMTRAT_LOG_DEBUG("smtrat.cad.projection", "\t-> " << coeff);
		cb(projection::normalize(coeff.toUnivariatePolynomial(variable)));
	}
}

/**
 * Implements the part of McCallums projection operator from @cite McCallum1985 that deals with two polynomials `p` and `q`:
 * \f$ \{ resultant(p, q) \} \f$
 */
template<typename Poly, typename Callback>
void paired(const Poly& p, const UPoly& q, carl::Variable variable, Callback&& cb) {
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "McCallum_paired(" << p << ", " << q << ", " << variable << ")");
	cb(projection::resultant(variable, p, q));
}

} // namespace mccallum
} // namespace projection
} // namespace cad
} // namespace smtrat
