#pragma once

#include "ProjectionOperator_McCallum.h"
#include "ProjectionOperator_utils.h"

namespace smtrat {
namespace cad {
namespace projection {

/**
 * Contains the implementation of an optimized version McCallums projection operator.
 * It is based on the observation by Brown that if some coefficient does not vanish only the leading coefficient is required.
 */
namespace mccallum_partial {

template<typename Poly, typename Callback>
void single(const Poly& p, carl::Variable variable, Callback&& cb) {
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "McCallum_partial_single(" << p << ", " << variable << ") -> Collins_single");
	cb(projection::discriminant(variable, p));

	for (std::size_t i = 0; i < p.coefficients().size(); ++i) {
		const auto& coeff = p.coefficients()[i];
		if (projection::doesNotVanish(coeff)) {
			if (i == 0) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "lcoeff = " << p.lcoeff() << " does not vanish. No coefficients needed.");
				return;
			} else {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "coeff " << coeff << " does not vanish. We only need the lcoeff() = " << p.lcoeff());
				cb(projection::normalize(p.lcoeff().toUnivariatePolynomial(variable)));
				return;
			}
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "All coefficients might vanish, we need all of them.");
	for (const auto& coeff : p.coefficients()) {
		if (coeff.isZero()) continue;
		assert(!coeff.isConstant());
		SMTRAT_LOG_DEBUG("smtrat.cad.projection", "\t-> " << coeff);
		cb(projection::normalize(coeff.toUnivariatePolynomial(variable)));
	}
}

template<typename Poly, typename Callback>
void paired(const Poly& p, const UPoly& q, carl::Variable variable, Callback&& cb) {
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "McCallum_partial_paired(" << p << ", " << q << ", " << variable << ")");
	mccallum::paired(p, q, variable, std::forward<Callback>(cb));
}

} // namespace mccallum_partial
} // namespace projection
} // namespace cad
} // namespace smtrat
