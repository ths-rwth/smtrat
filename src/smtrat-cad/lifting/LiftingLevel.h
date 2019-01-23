#pragma once


#include <carl/interval/Interval.h>
#include "../common.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class LiftingLevel {
	public:
		using Interval = carl::Interval;
	private:
		const Constraints& mConstraints;
		std::vector<carl::Variable> mVariables;
		Sample curSample;
		std::vector<UPoly&> polynoms;
		std::vector<Interval> intervals;
		std::set<RAN> levelintervals;
        LiftingLevel predecessor;
		
		std::size_t dim() const {
			return mVariables.size();
		}

		void addInterval(Interval inter) {
			intervals.insert(inter);
			levelintervals.insert(inter.lower());
			levelintervals.insert(inter.upper());
		}
		
	public:


	};
}
}
