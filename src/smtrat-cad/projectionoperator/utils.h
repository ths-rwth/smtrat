#pragma once

#include <carl-arith/poly/umvpoly/functions/Factorization.h>
#include <carl-arith/poly/umvpoly/functions/PrimitivePart.h>
#include <carl-arith/poly/umvpoly/functions/Resultant.h>
#include <carl-arith/poly/umvpoly/functions/SquareFreePart.h>
#include <carl-arith/poly/umvpoly/functions/to_univariate_polynomial.h>

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
	if (is_zero(p)) return false;
	if (p.is_constant()) return true;
	auto def = carl::definiteness(p);
	if (def == carl::Definiteness::POSITIVE) return true;
	if (def == carl::Definiteness::NEGATIVE) return true;
	return false;
}

/**
 * Normalizes the given Poly by removing constant and duplicate factors.
 */
template<typename Poly>
Poly normalize(const Poly& p) {
	auto res = carl::pseudo_primitive_part(carl::squareFreePart(p)).normalized();
	SMTRAT_LOG_TRACE("smtrat.cad.projection", "Normalizing " << p << " to " << res);
	return res;
}

/**
 * Computes the resultant of two polynomials.
 * The polynomials are assumed to be univariate polynomials and thus know their respective main variables.
 * The given variable instead indicates the main variable of the resulting polynomial.
 * @param variable Main variable of the resulting polynomial.
 * @param p First input polynomial.
 * @param q Second input polynomial.
 * @return Resultant of p and q in main variable variable.
 */
template<typename Poly>
Poly resultant(carl::Variable variable, const Poly& p, const Poly& q) {
	auto res = normalize(carl::switch_main_variable(carl::resultant(p,q), variable));
	SMTRAT_LOG_TRACE("smtrat.cad.projection", "resultant(" << p << ", " << q << ") = " << res);
	return res;
}

/**
 * Computes the discriminant of a polynomial.
 * The polynomial is assumed to be univariate and thus knows is main variable.
 * The given variable instead indicates the main variable of the resulting polynomial.
 * @param variable Main variable of the resulting polynomial.
 * @param p Input polynomial.
 * @return Discriminant of p in main variable variable.
 */
template<typename Poly>
Poly discriminant(carl::Variable variable, const Poly& p) {
	auto dis = normalize(carl::switch_main_variable(carl::discriminant(p), variable));
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
		while (!is_zero(this->back())) {
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
	return carl::principalSubresultantsCoefficients(p, q);
}

template<typename Poly, typename Callback>
void returnPoly(const Poly& p, Callback&& cb) {
	if (true) {
		for (const auto& fact: carl::factorization(carl::MultivariatePolynomial<Rational>(p), false)) {
			auto uf = carl::to_univariate_polynomial(fact.first, p.main_var());
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> " << uf);
			cb(uf);
		}
	} else {
		SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> " << p);
		cb(p);
	}
}

} // namespace projection
} // namespace cad
} // namespace smtrat
