#pragma once

#include "McCallum.h"
#include "utils.h"

namespace smtrat {
namespace cad {
namespace projection {

/**
 * Contains the implementation of Browns projection operator as specified in @cite Brown01 after Theorem 3.1.
 */
namespace lazard {

/**
 * Implements the part of Lazards projection operator from @cite Lazard94 that deals with a single polynomial `p`:
 * \f$ \{ leading_coeff(p), trailing_coeff(p), discriminant(p) \} \f$
 */
template<typename Poly, typename Callback>
void single(const Poly& p, carl::Variable variable, Callback&& cb) {
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Brown_single(" << p << ")");
	returnPoly(projection::discriminant(variable, p), cb);
	returnPoly(projection::normalize(p.lcoeff().toUnivariatePolynomial(variable)), cb);
	returnPoly(projection::normalize(p.tcoeff().toUnivariatePolynomial(variable)), cb);
}

/**
 * Implements the part of Lazard projection operator from @cite Lazard94 that deals with two polynomials `p` and `q` which is just the respective part of McCallums projection operator mccallum::paired.
 */
template<typename Poly, typename Callback>
void paired(const Poly& p, const UPoly& q, carl::Variable variable, Callback&& cb) {
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Brown_paired(" << p << ", " << q << ") -> McCallum_paired");
	mccallum::paired(p, q, variable, std::forward<Callback>(cb));
}

} // namespace lazard
} // namespace projection
} // namespace cad
} // namespace smtrat
