#pragma once

#include "ProjectionOperator_Collins.h"
#include "ProjectionOperator_utils.h"

namespace smtrat {
namespace cad {
namespace projection {

/**
 * Contains the implementation of Hongs projection operator as specified in @cite Hong1990 in Section 2.2.
 */
namespace hong {

/**
 * Implements the part of Hongs projection operator from @cite Hong1990 that deals with a single polynomial `p` which is just the respective part of Collins' projection operator collins::single.
 */
template<typename Poly, typename Callback>
void single(const Poly& p, carl::Variable variable, Callback&& cb) {
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Hong_single(" << p << ", " << variable << ") -> Collins_single");
	collins::single(p, variable, std::forward<Callback>(cb));
}

/**
 * Implements the part of Hongs projection operator from @cite Hong1990 that deals with two polynomials `p` and `q`:
 * \f$ \bigcup_{F \in RED(p)} PSC(F, q) \f$
 */
template<typename Poly, typename Callback>
void paired(const Poly& p, const UPoly& q, carl::Variable variable, Callback&& cb) {
	SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Hong_paired(" << p << ", " << q << ", " << variable << ")");
	projection::Reducta<Poly> RED_p(p);
	for (const auto& reducta_p : RED_p) {
		for (const auto& psc : projection::PSC(reducta_p, q)) {
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "reducta pcs: " << psc);
			cb(projection::normalize(psc.switchVariable(variable)));
		}
	}
}

} // namespace hong
} // namespace projection
} // namespace cad
} // namespace smtrat
