#pragma once

#include <smtrat-common/smtrat-common.h>

namespace smtrat::analyzer {

struct DegreeCollector {
	std::size_t degree_max = 0;
	std::size_t degree_sum = 0;
	std::size_t tdegree_max = 0;
	std::size_t tdegree_sum = 0;

	void operator()(const Poly& p) {
		degree_max = std::max(degree_max, p.totalDegree());
		degree_sum += p.totalDegree();
		tdegree_max = std::max(tdegree_max, p.totalDegree());
		tdegree_sum += p.totalDegree();
	}
	void operator()(const carl::UnivariatePolynomial<Poly>& p) {
		degree_max = std::max(degree_max, p.degree());
		degree_sum += p.degree();
		tdegree_max = std::max(tdegree_max, p.totalDegree());
		tdegree_sum += p.totalDegree();
	}
	void operator()(const ConstraintT& c) {
		(*this)(c.lhs());
	}
};

}