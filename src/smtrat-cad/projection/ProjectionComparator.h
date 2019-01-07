#pragma once

#include "../common.h"
#include "../Settings.h"

#include <tuple>

namespace smtrat {
namespace cad {

namespace projection_compare {
	
	template<typename Poly>
	using Candidate = std::tuple<const Poly&, const Poly&, std::size_t>;
	template<typename Poly>
	std::ostream& operator<<(std::ostream& os, const Candidate<Poly>& c) {
		return os << "(" << std::get<0>(c) << ", " << std::get<1>(c) << " on " << std::get<2>(c) << ")";
	}

	struct level {};
	struct degree {};
	struct type {};

	template<typename Poly>
	auto get(const Candidate<Poly>& c, level) {
		return std::get<2>(c);
	}
	template<typename Poly>
	auto get(const Candidate<Poly>& c, degree) {
		return std::max(std::get<0>(c).complexity(), std::get<1>(c).complexity());
	}
	template<typename Poly>
	auto get(const Candidate<Poly>& c, type) {
		if (&std::get<0>(c) == &std::get<1>(c)) return 0;
		return 1;
	}

	/**
	 * Compares the criterion given by `t` of two samples `lhs` and `rhs` using a comparator `f`.
	 * Returns `0` if the values are the same, `-1` if `lhs` should be used first and `1` if `rhs` should be used first.
	 */
	template<typename Poly, typename tag, typename F>
	int compareCriterion(const Candidate<Poly>& lhs, const Candidate<Poly>& rhs, tag t, F&& f) {
		auto l = get(lhs, t);
		auto r = get(rhs, t);
		if (l == r) {
			SMTRAT_LOG_TRACE("smtrat.cad.projectioncompare", "Comparing " << l << " < " << r << " -> 0");
			return 0;
		}
		SMTRAT_LOG_TRACE("smtrat.cad.projectioncompare", "Comparing " << l << " < " << r << " ? " << (f(l, r) ? -1 : 1));
		return f(l, r) ? -1 : 1;
	}
	
	template<typename Poly>
	bool compare(const Candidate<Poly>& lhs, const Candidate<Poly>& rhs) {
		return lhs < rhs;
	}
	template<typename Poly, typename tag, typename F, typename... Tail>
	bool compare(const Candidate<Poly>& lhs, const Candidate<Poly>& rhs) {
		int res = compareCriterion(lhs, rhs, tag{}, F{});
		if (res != 0) return res > 0;
		return compare<Poly, Tail...>(lhs, rhs);
	}
	
	template<typename... Args>
	struct ProjectionComparator_impl {
		template<typename Poly>
		bool operator()(const Candidate<Poly>& lhs, const Candidate<Poly>& rhs) const {
			auto res = compare<Poly, Args...>(lhs, rhs);
			SMTRAT_LOG_TRACE("smtrat.cad.projectioncompare", lhs << " < " << rhs << " ? " << res);
			return res;
		}
	};
	
	using lt = std::less<>;
	using gt = std::greater<>;
	
	template<ProjectionCompareStrategy Strategy>
	struct ProjectionComparator {};
	
	template<>
	struct ProjectionComparator<ProjectionCompareStrategy::D>:
		ProjectionComparator_impl<degree, lt> {};
	template<>
	struct ProjectionComparator<ProjectionCompareStrategy::PD>:
		ProjectionComparator_impl<type, gt, degree, lt> {};
	template<>
	struct ProjectionComparator<ProjectionCompareStrategy::SD>:
		ProjectionComparator_impl<type, lt, degree, lt> {};
	template<>
	struct ProjectionComparator<ProjectionCompareStrategy::lD>:
		ProjectionComparator_impl<level, lt, degree, lt> {};
	template<>
	struct ProjectionComparator<ProjectionCompareStrategy::LD>:
		ProjectionComparator_impl<level, gt, degree, lt> {};
						
}

	using projection_compare::ProjectionComparator;
	
	template<typename Poly>
	projection_compare::Candidate<Poly> candidate(const Poly& p, const Poly& q, std::size_t level) {
		return projection_compare::Candidate<Poly>(p, q, level);
	}
}
}
