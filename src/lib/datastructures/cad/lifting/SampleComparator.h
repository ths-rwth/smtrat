#pragma once

#include "Sample.h"
#include "../Common.h"
#include "../Settings.h"

namespace smtrat {
namespace cad {
	template<typename Iterator, SampleCompareStrategy Strategy>
	struct SampleComparator {};
	
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::Value> {
		bool operator()(const Iterator& lhs, const Iterator& rhs) const {
			std::size_t lsize = lhs->value().size();
			std::size_t rsize = rhs->value().size();
			if (lsize != rsize) {
				SMTRAT_LOG_TRACE("smtrat.cad.lifting", lhs->value() << " < " << rhs->value() << ": Size (" << lsize << " / " << rsize << ") " << (lsize > rsize));
				return lsize > rsize;
			}
			SMTRAT_LOG_TRACE("smtrat.cad.lifting", lhs->value() << " < " << rhs->value() << ": Absolute " << (lhs->value().abs() > rhs->value().abs()));
			return lhs->value().abs() > rhs->value().abs();
		}
	};
	
	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::Numeric> {
		using Fallback = SampleComparator<Iterator, SampleCompareStrategy::Value>;
		bool operator()(const Iterator& lhs, const Iterator& rhs) const {
			bool lint = lhs->value().isNumeric();
			bool rint = rhs->value().isNumeric();
			if (lint && rint) return Fallback()(lhs, rhs);
			if (lint || rint) {
				SMTRAT_LOG_TRACE("smtrat.cad.lifting", lhs->value() << " < " << rhs->value() << ": Num " << rint);
				return rint;
			}
			return Fallback()(lhs, rhs);
		}
	};

	template<typename Iterator>
	struct SampleComparator<Iterator, SampleCompareStrategy::Integer> {
		using Fallback = SampleComparator<Iterator, SampleCompareStrategy::Numeric>;
		bool operator()(const Iterator& lhs, const Iterator& rhs) const {
			bool lint = lhs->value().isIntegral();
			bool rint = rhs->value().isIntegral();
			if (lint && rint) return Fallback()(lhs, rhs);
			if (lint || rint) {
				SMTRAT_LOG_TRACE("smtrat.cad.lifting", lhs->value() << " < " << rhs->value() << ": Int " << rint);
				return rint;
			}
			return Fallback()(lhs, rhs);
		}
	};
	
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
