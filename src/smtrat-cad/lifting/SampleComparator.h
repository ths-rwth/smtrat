#pragma once

#include "Sample.h"
#include "../common.h"
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
		return carl::bitsize(it->value());
	}
	template<typename It>
	auto get(const It& it, absvalue) {
		return carl::abs(it->value());
	}
	template<typename It>
	auto get(const It& it, type) {
		if (!it->value().is_numeric()) return 0;
		if (!carl::is_integer(it->value())) return 1;
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
		if (res != 0) return res > 0;
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
		bool operator()(const Iterator& lhs, const Iterator& rhs) const {
			SMTRAT_LOG_TRACE("smtrat.cad.samplecompare", *lhs << " < " << *rhs << "?");
			auto c = compare(lhs, rhs);
			auto r = reference(lhs, rhs);
			SMTRAT_LOG_TRACE("smtrat.cad.samplecompare", "-> " << c << " / " << r);
			assert(c == r);
			return c;
		}
		bool reference(const Iterator& lhs, const Iterator& rhs) const {
			SampleComparator_impl<Iterator, type, gt, size, lt, absvalue, lt> sc;
			auto res = sc(lhs, rhs);
			SMTRAT_LOG_TRACE("smtrat.cad.samplecompare", *lhs << " < " << *rhs << " -> " << res);
			return res;
		}
		bool compare(const Iterator& lhs, const Iterator& rhs) const {
			bool l1 = carl::is_integer(lhs->value());
			bool r1 = carl::is_integer(rhs->value());
			SMTRAT_LOG_TRACE("smtrat.cad.samplecompare", lhs->value() << " < " << rhs->value() << ": Int " << r1);
			if (l1 != r1) {
				return r1;
			}
			bool l2 = lhs->value().is_numeric();
			bool r2 = rhs->value().is_numeric();
			SMTRAT_LOG_TRACE("smtrat.cad.samplecompare", lhs->value() << " < " << rhs->value() << ": Num " << r2);
			if (l2 != r2) {
				return r2;
			}
			std::size_t l3 = carl::bitsize(lhs->value());
			std::size_t r3 = carl::bitsize(rhs->value());
			SMTRAT_LOG_TRACE("smtrat.cad.samplecompare", lhs->value() << " < " << rhs->value() << ": Size (" << l3 << " / " << r3 << ") " << (l3 > r3));
			if (l3 != r3) {
				return l3 > r3;
			}
			SMTRAT_LOG_TRACE("smtrat.cad.samplecompare", lhs->value() << " < " << rhs->value() << ": Absolute " << (carl::abs(lhs->value()) >= carl::abs(rhs->value())));
			if (carl::abs(lhs->value()) != carl::abs(rhs->value())) return carl::abs(lhs->value()) >= carl::abs(rhs->value());
			return lhs < rhs;
		}
	};
	
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::T>:
		SampleComparator_impl<Iterator, type, gt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::TLSA>:
		SampleComparator_impl<Iterator, type, gt, level, gt, size, lt, absvalue, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::TSA>:
		SampleComparator_impl<Iterator, type, gt, size, lt, absvalue, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::TS>:
		SampleComparator_impl<Iterator, type, gt, size, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LT>:
		SampleComparator_impl<Iterator, level, gt, type, gt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LTA>:
		SampleComparator_impl<Iterator, level, gt, type, gt, absvalue, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LTS>:
		SampleComparator_impl<Iterator, level, gt, type, gt, size, lt> {};
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::LTSA>:
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
	template<typename Iterator>
	struct FullSampleComparator<Iterator, FullSampleCompareStrategy::T>: SampleComparator<Iterator, SampleCompareStrategy::T> {};
}
}
