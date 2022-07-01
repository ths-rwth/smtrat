#pragma once

#include "utils.h"

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
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "McCallum_single(" << p << ")");
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "\t-> discriminant " << projection::discriminant(variable, p));
	cb(projection::discriminant(variable, p));
	for (const auto& coeff : p.coefficients()) {
		if (coeff.is_constant()) continue;
		SMTRAT_LOG_DEBUG("smtrat.cad.projection", "\t-> coefficient " << coeff);
		returnPoly(projection::normalize(carl::to_univariate_polynomial(coeff, variable)), cb);
	}
}

/**
 * Implements the part of McCallums projection operator from @cite McCallum1985 that deals with two polynomials `p` and `q`:
 * \f$ \{ resultant(p, q) \} \f$
 */
template<typename Poly, typename Callback>
void paired(const Poly& p, const UPoly& q, carl::Variable variable, Callback&& cb) {
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "McCallum_paired(" << p << ", " << q << ")");
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "\t-> resultant " << projection::resultant(variable, p, q));
	returnPoly(projection::resultant(variable, p, q), cb);
}

} // namespace mccallum
} // namespace projection
} // namespace cad
} // namespace smtrat
