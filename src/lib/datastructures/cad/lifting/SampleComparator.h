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
	struct type {};

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
	auto get(const It& it, type) {
		if (!it->value().isNumeric()) return 0;
		if (!it->value().isIntegral()) return 1;
		return 2;
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

	//template<typename Iterator>
	//struct SampleComparator<Iterator, SampleCompareStrategy::Type>:
	//	SampleComparator_impl<Iterator, type, gt, size, lt> {};
	
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::Type> {
		bool operator()(const It& lhs, const It& rhs) const {
			assert(compare(lhs, rhs) == reference(lhs, rhs));
			return compare(lhs, rhs);
		}
		bool reference(const It& lhs, const It& rhs) const {
			SampleComparator_impl<Iterator, type, gt, size, lt, absvalue, lt> sc;
			return sc(lhs, rhs);
		}
		bool compare(const It& lhs, const It& rhs) const {
			bool l1 = lhs->value().isIntegral();
			bool r1 = rhs->value().isIntegral();
			if (l1 != r1) {
				SMTRAT_LOG_TRACE("smtrat.cad.lifting", lhs->value() << " < " << rhs->value() << ": Int " << rint);
				return r1;
			}
			bool l2 = lhs->value().isNumeric();
			bool r2 = rhs->value().isNumeric();
			if (l2 != r2) {
				SMTRAT_LOG_TRACE("smtrat.cad.lifting", lhs->value() << " < " << rhs->value() << ": Num " << rint);
				return r2;
			}
			std::size_t l3 = lhs->value().size();
			std::size_t r3 = rhs->value().size();
			if (l3 != r3) {
				SMTRAT_LOG_TRACE("smtrat.cad.lifting", lhs->value() << " < " << rhs->value() << ": Size (" << lsize << " / " << rsize << ") " << (lsize > rsize));
				return l3 > r3;
			}
			SMTRAT_LOG_TRACE("smtrat.cad.lifting", lhs->value() << " < " << rhs->value() << ": Absolute " << (lhs->value().abs() > rhs->value().abs()));
			return lhs->value().abs() > rhs->value().abs();
		}
	};
	
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::I>:
		SampleComparator_impl<Iterator, type, gt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::ILSA>:
		SampleComparator_impl<Iterator, type, gt, level, gt, size, lt, absvalue, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::ISA>:
		SampleComparator_impl<Iterator, type, gt, size, lt, absvalue, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::IS>:
		SampleComparator_impl<Iterator, type, gt, size, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LI>:
		SampleComparator_impl<Iterator, level, gt, type, gt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LIA>:
		SampleComparator_impl<Iterator, level, gt, type, gt, absvalue, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LIS>:
		SampleComparator_impl<Iterator, level, gt, type, gt, size, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LISA>:
		SampleComparator_impl<Iterator, level, gt, type, gt, size, lt, absvalue, lt> {};
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
	struct FullSampleComparator<Iterator, FullSampleCompareStrategy::Type>: SampleComparator<Iterator, SampleCompareStrategy::Type> {};
}
}
