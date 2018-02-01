#pragma once

#include "Sample.h"
#include "../Common.h"
#include "../Settings.h"

namespace smtrat {
namespace cad {

/**
 * Contains comparison operators for samples and associated helpers.
 * The comparators implement a `less-than` operators and large samples are considered first.
 * Hence if `lhs` has greater priority than `rhs`, the result should be `false`.
 */
namespace sample_compare {

	struct level {};
	struct size {};
	struct absvalue {};
	struct numeric {};
	struct integer {};

	template<typename It>
	auto get(const It& it, level) {
		return it.depth();
	}
	template<typename It>
	auto get(const It& it, size) {
		return it->value().size();
	}
	template<typename It>
	auto get(const It& it, absvalue) {
		return it->value().abs();
	}
	template<typename It>
	auto get(const It& it, numeric) {
		return it->value().isNumeric();
	}
	template<typename It>
	auto get(const It& it, integer) {
		return it->value().isIntegral();
	}

	/**
	 * Compares the criterion given by `t` of two samples `lhs` and `rhs` using a comparator `f`.
	 * Returns `0` if the values are the same, `-1` if `lhs` should be used first and `1` if `rhs` should be used first.
	 */
	template<typename It, typename tag, typename F>
	int compareCriterion(const It& lhs, const It& rhs, tag t, F&& f) {
		auto l = get(lhs, t);
		auto r = get(rhs, t);
		if (l == r) {
			SMTRAT_LOG_TRACE("smtrat.cad.samplecompare", "Comparing " << l << " < " << r << " -> 0");
			return 0;
		}
		SMTRAT_LOG_TRACE("smtrat.cad.samplecompare", "Comparing " << l << " < " << r << " ? " << (f(l, r) ? -1 : 1));
		return f(l, r) ? -1 : 1;
	}
	
	template<typename It>
	bool compare(const It& lhs, const It& rhs) {
		return lhs < rhs;
	}
	template<typename It, typename tag, typename F, typename... Tail>
	bool compare(const It& lhs, const It& rhs) {
		int res = compareCriterion(lhs, rhs, tag{}, F{});
		if (res != 0) return res < 0;
		return compare<It, Tail...>(lhs, rhs);
	}
	
	template<typename It, typename... Args>
	struct SampleComparator_impl {
		bool operator()(const It& lhs, const It& rhs) const {
			auto res = compare<It, Args...>(lhs, rhs);
			SMTRAT_LOG_TRACE("smtrat.cad.samplecompare", *lhs << " < " << *rhs << " ? " << res);
			return res;
		}
	};
	
	using lt = std::less<>;
	using gt = std::greater<>;
	
	template<typename Iterator, SampleCompareStrategy Strategy>
	struct SampleComparator {};
	
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::Value>:
		SampleComparator_impl<Iterator, size, lt> {};
	
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::Numeric>:
		SampleComparator_impl<Iterator, numeric, gt, size, lt> {};

	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::Integer>:
		SampleComparator_impl<Iterator, integer, gt, numeric, gt, size, lt> {};
	
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::I>:
		SampleComparator_impl<Iterator, integer, gt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::ILSA>:
		SampleComparator_impl<Iterator, integer, gt, level, gt, size, lt, absvalue, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::ISA>:
		SampleComparator_impl<Iterator, integer, gt, size, lt, absvalue, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::IS>:
		SampleComparator_impl<Iterator, integer, gt, size, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LI>:
		SampleComparator_impl<Iterator, level, gt, integer, gt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LIA>:
		SampleComparator_impl<Iterator, level, gt, integer, gt, absvalue, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LIS>:
		SampleComparator_impl<Iterator, level, gt, integer, gt, size, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LISA>:
		SampleComparator_impl<Iterator, level, gt, integer, gt, size, lt, absvalue, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LS>:
		SampleComparator_impl<Iterator, level, gt, size, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::S>:
		SampleComparator_impl<Iterator, size, lt> {};
}

	using sample_compare::SampleComparator;

	template<typename Iterator, FullSampleCompareStrategy Strategy>
	struct FullSampleComparator {};
	
	template<typename Iterator>
	struct FullSampleComparator<Iterator, FullSampleCompareStrategy::Value>: SampleComparator<Iterator, SampleCompareStrategy::Value> {};
	template<typename Iterator>
	struct FullSampleComparator<Iterator, FullSampleCompareStrategy::Numeric>: SampleComparator<Iterator, SampleCompareStrategy::Numeric> {};
	template<typename Iterator>
	struct FullSampleComparator<Iterator, FullSampleCompareStrategy::Integer>: SampleComparator<Iterator, SampleCompareStrategy::Integer> {};
}
}
