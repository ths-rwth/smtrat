#pragma once

#include <smtrat-cadcells/common.h>
#include <smtrat-cadcells/operators/operator.h>

namespace smtrat::cadcells::representation::approximation {

class LinearSegment {
private:
	Rational m_slope;
	Rational m_intercept;
	carl::Interval<Rational> m_domain;

    std::optional<datastructures::PolyRef> m_poly_ref;
public:
	LinearSegment() = default;
	LinearSegment(const Rational& slope, const Rational& intercept, const carl::Interval<Rational>& domain)
    : m_slope(slope), m_intercept(intercept), m_domain(domain) {
		assert(domain.lower() < domain.upper());
	}
	LinearSegment(const Rational& a_x, const Rational& a_y, const Rational& b_x, const Rational& b_y) {
		m_slope = (b_y - a_y) / (b_x - a_x);
		m_intercept = a_y - (m_slope * a_x);
		m_domain = carl::Interval<Rational>(a_x, b_x);
	}

	const carl::Interval<Rational>& domain() const { return m_domain; }

	Rational evaluate(const Rational& x) const { return m_slope * x + m_intercept; }

	datastructures::PolyRef poly_ref(datastructures::PolyPool &polys, carl::LPPolynomial::ContextType &ctx, carl::Variable var_x, carl::Variable var_y) {
		if(m_poly_ref) { return *m_poly_ref; }

		Rational c1 = m_slope.get_num() * m_intercept.get_den();
		Rational c2 = m_slope.get_den() * m_intercept.get_num();
		Rational c3 = m_slope.get_den() * m_intercept.get_den();

		using P = Polynomial;

		Polynomial res = (P(ctx, var_x) * P(ctx, c1)) + (P(ctx, c2)) - (P(ctx, var_y) * P(ctx, c3));

		m_poly_ref = polys(res);
		return *m_poly_ref;
	}

	// operator<<
	friend std::ostream& operator<<(std::ostream& os, const LinearSegment& segment) {
		os << segment.m_slope << " * x + " << segment.m_intercept;
		return os;
	}
};


}