#pragma once

#include "Sample.h"

namespace smtrat {
namespace cad {
	template<typename Iterator>
	struct SampleComparator {
		bool operator()(const Iterator& lhs, const Iterator& rhs) const {
			const Sample& l = *lhs;
			const Sample& r = *rhs;
			return l.value() < r.value();
		}
	};
	
	template<typename Iterator>
	struct FullSampleComparator {
		bool operator()(const Iterator& lhs, const Iterator& rhs) const {
			const Sample& l = *lhs;
			const Sample& r = *rhs;
			return l.value() < r.value();
		}
	};
}
}
