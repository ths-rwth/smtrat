#pragma once

#include "utils.h"

#include <carl-arith/poly/umvpoly/functions/Derivative.h>

namespace smtrat {
namespace cad {
namespace projection {

/**
 * Contains the implementation of Collins projection operator as specified in @cite Collins1975 below Theorem 4.
 */
namespace collins {

/**
 * Implements the part of Collins projection operator from @cite Collins1975 that deals with a single polynomial `p`:
 * \f$ \bigcup_{B \in RED(p)} \{ ldcf(B) \} \cup PSC(B, B') \f$
 */
template<typename Poly, typename Callback>
void single(const Poly& p, carl::Variable variable, Callback&& cb) {
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Collins_single(" << p << ")");

	// Separate into
	// - leading coefficients of reducta which are all coefficients
	// - PSC of all reducta
	for (const auto& coeff : p.coefficients()) {
		SMTRAT_LOG_DEBUG("smtrat.cad.projection", "reductum lcoeff: " << coeff);
		returnPoly(projection::normalize(carl::to_univariate_polynomial(coeff, variable)), cb);
	}

	projection::Reducta<Poly> RED_p(p);
	projection::Reducta<Poly> RED_d(carl::derivative(p));
	for (std::size_t i = 0; i < RED_d.size(); ++i) {
		const auto& reducta = RED_p[i];
		const auto& reducta_derivative = RED_d[i];
		for (const auto& psc : projection::PSC(reducta, reducta_derivative)) {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "reducta psc: " << psc);
			returnPoly(projection::normalize(carl::switch_main_variable(psc, variable)), cb);
		}
	}
}

/**
 * Implements the part of Collins projection operator from @cite Collins1975 that deals with two polynomials `p` and `q`:
 * \f$ \bigcup_{B_1 \in RED(p), B_2 \in RED(q)} PSC(B_1, B_2) \f$
 */
template<typename Poly, typename Callback>
void paired(const Poly& p, const UPoly& q, carl::Variable variable, Callback&& cb) {
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Collins_paired(" << p << ", " << q << ")");
	projection::Reducta<Poly> RED_p(p);
	projection::Reducta<Poly> RED_q(q);
	for (const auto& reducta_p : RED_p) {
		for (const auto& reducta_q : RED_q) {
			for (const auto& psc : projection::PSC(reducta_p, reducta_q)) {
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "reducta psc: " << psc);
				returnPoly(projection::normalize(carl::switch_main_variable(psc, variable)), cb);
			}
		}
	}
}

} // namespace collins
} // namespace projection
} // namespace cad
} // namespace smtrat
