#pragma once

#include <carl/core/rootfinder/RootFinder.h>

#include "../common.h"

namespace smtrat {
namespace cad {

	template<typename Iterator, typename Settings>
	class LiftingOperator {
	private:
	public:
		template<typename Tree>
		std::vector<Iterator> operator()(Iterator sample, const UPoly& p, Tree& tree) const {
			//std::map<Variable, RealAlgebraicNumber<Number>> m;
			//Interval<Number> bounds;
			std::vector<Iterator> res;
			//for (const auto& r: carl::rootfinder::realRoots(p, m, bounds, Settings::rootSplittingStrategy)) {
			//	res.push_back(tree.append(sample, r));
			//}
			return res;
		}
	};

}
}
