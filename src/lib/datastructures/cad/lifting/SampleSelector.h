#pragma once

#include "../Common.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class SampleSelector {
	public:
		RAN below(const RAN& upper)	const {
			if (upper.isNumeric()) {
				return RAN(carl::ceil(upper.value()) - 1, false);
			} else {
				return RAN(carl::ceil(upper.lower()) - 1, false);
			}
		}
		
		RAN between(const RAN& lower, const RAN& upper) const {
			RationalInterval i;
			if (lower.isNumeric()) i.setLower(lower.value());
			else i.setLower(lower.upper());
			if (upper.isNumeric()) i.setUpper(upper.value());
			else i.setUpper(upper.lower());
			return RAN(i.sample(false), false);
		}
		
		RAN above(const RAN& lower)	const {
			if (lower.isNumeric()) {
				return RAN(carl::floor(lower.value()) + 1, false);
			} else {
				return RAN(carl::floor(lower.upper()) + 1, false);
			}
		}
	};
}
}
