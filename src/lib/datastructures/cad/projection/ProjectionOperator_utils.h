#pragma once

namespace smtrat {
namespace cad {
namespace projection {

/**
 * Tries to determine whether the given Poly vanishes for some assignment.
 * Returns true if the Poly is guaranteed not to vanish.
 * Returns false otherwise.
 */
template<typename Poly>
bool doesNotVanish(const Poly& p) {
	if (p.isZero()) return false;
	if (p.isConstant()) return true;
	auto def = p.definiteness();
	if (def == carl::Definiteness::POSITIVE) return true;
	if (def == carl::Definiteness::NEGATIVE) return true;
	return false;
}

/**
 * Normalizes the given Poly by removing constant and duplicate factors.
 */
template<typename Poly>
Poly normalize(const Poly& p) {
	SMTRAT_LOG_TRACE("smtrat.cad.projection", "Normalizing " << p << " to " << p.squareFreePart().pseudoPrimpart().normalized());
	return p.squareFreePart().pseudoPrimpart().normalized();
}

/**
 * Computes the resultant of two polynomials with respect to the given variable.
 */
template<typename Poly>
Poly resultant(carl::Variable variable, const Poly& p, const Poly& q) {
	auto res = normalize(p.resultant(q).switchVariable(variable));
	SMTRAT_LOG_TRACE("smtrat.cad.projection", "resultant(" << p << ", " << q << ") = " << res);
	return res;
}

/**
 * Computes the discriminant of a polynomial with respect to the given variable.
 */
template<typename Poly>
Poly discriminant(carl::Variable variable, const Poly& p) {
	auto dis = normalize(p.discriminant().switchVariable(variable));
	SMTRAT_LOG_TRACE("smtrat.cad.projection", "discriminant(" << p << ") = " << dis);
	return dis;
}

/**
 * Construct the set of reducta of the given polynomial.
 * This only adds a custom constructor to a std::
 */
template<typename Poly>
struct Reducta : std::vector<Poly> {
	Reducta(const Poly& p) {
		this->emplace_back(p);
		while (!this->back().isZero()) {
			this->emplace_back(this->back());
			this->back().truncate();
		}
		this->pop_back();
		SMTRAT_LOG_TRACE("smtrat.cad.projection", "Reducta of " << p << " = " << *this);
	}
};

/**
 * Computes the Principal Subresultant Coefficients of two polynomials.
 */
template<typename Poly>
std::vector<Poly> PSC(const Poly& p, const Poly& q) {
	return Poly::principalSubresultantsCoefficients(p, q);
}

} // namespace projection
} // namespace cad
} // namespace smtrat
