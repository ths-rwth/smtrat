#pragma once

#include "../Common.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class SampleSelector {
	public:
		RAN below(const RAN& upper)	const {
			SMTRAT_LOG_TRACE("smtrat.cad.sampling", "Selecting from (-oo, " << upper << ")");
			if (upper.isNumeric()) {
				SMTRAT_LOG_TRACE("smtrat.cad.sampling", "-> " << (carl::ceil(upper.value()) - 1));
				return RAN(carl::ceil(upper.value()) - 1, false);
			} else {
				SMTRAT_LOG_TRACE("smtrat.cad.sampling", "-> " << (carl::ceil(upper.lower()) - 1));
				return RAN(carl::ceil(upper.lower()) - 1, false);
			}
		}
		
		RAN between(const RAN& lower, const RAN& upper) const {
			SMTRAT_LOG_TRACE("smtrat.cad.sampling", "Selecting from (" << lower << ", " << upper << ")");
			RationalInterval i;
			if (lower.isNumeric()) i.set(lower.value(), lower.value());
			else i.set(lower.upper(), lower.upper());
			if (upper.isNumeric()) i.setUpper(upper.value());
			else i.setUpper(upper.lower());
			while (i.isEmpty()) {
				if (!lower.isNumeric()) {
					lower.refine();
					if (lower.isNumeric()) i.setLower(lower.value());
					else i.setLower(lower.upper());
				}
				if (!upper.isNumeric()) {
					upper.refine();
					if (upper.isNumeric()) i.setUpper(upper.value());
					else i.setUpper(upper.lower());
				}
			}
			SMTRAT_LOG_TRACE("smtrat.cad.sampling", "-> " << i.sample(false) << " from " << i);
			return RAN(i.sample(false), false);
		}
		
		RAN above(const RAN& lower)	const {
			SMTRAT_LOG_TRACE("smtrat.cad.sampling", "Selecting from (" << lower << ", oo)");
			if (lower.isNumeric()) {
				SMTRAT_LOG_TRACE("smtrat.cad.sampling", "-> " << (carl::floor(lower.value()) + 1));
				return RAN(carl::floor(lower.value()) + 1, false);
			} else {
				SMTRAT_LOG_TRACE("smtrat.cad.sampling", "-> " << (carl::floor(lower.upper()) + 1));
				return RAN(carl::floor(lower.upper()) + 1, false);
			}
		}
	};
}
}
