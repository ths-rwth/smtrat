#pragma once

#include <smtrat-common/smtrat-common.h>

#include <carl-arith/poly/umvpoly/functions/Degree.h>

namespace smtrat::analyzer {

struct DegreeCollector {
	std::size_t degree_max = 0;
	std::size_t degree_sum = 0;
	std::size_t tdegree_max = 0;
	std::size_t tdegree_sum = 0;

	void operator()(const Poly& p) {
		degree_max = std::max(degree_max, carl::total_degree(p));
		degree_sum += carl::total_degree(p);
		tdegree_max = std::max(tdegree_max, carl::total_degree(p));
		tdegree_sum += carl::total_degree(p);
	}
	void operator()(const carl::UnivariatePolynomial<Poly>& p) {
		degree_max = std::max(degree_max, p.degree());
		degree_sum += p.degree();
		tdegree_max = std::max(tdegree_max, carl::total_degree(p));
		tdegree_sum += carl::total_degree(p);
	}
	void operator()(const ConstraintT& c) {
		(*this)(c.lhs());
	}
};

}