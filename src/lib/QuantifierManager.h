/**
 * @file QuantifierManager.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#include <algorithm>
#include <set>

#include "Common.h"
#include "Formula.h"

#pragma once

namespace smtrat {

class QuantifierManager {
private:
	QuantifiedVariables mData;

	/**
	 * Calculates the intersection of two sets a and b and checks if this intersection is not empty.
	 * The intersection is added to a given third set c.
     * @param a First set.
     * @param b Second set.
     * @param c Third set.
     * @return If intersection is not empty.
     */
	template<typename T>
	bool intersect(const std::set<T>& a, const std::set<T>& b, std::set<T>& c) const {
		size_t s = c.size();
		std::set_intersection(
			a.begin(), a.end(),
			b.begin(), b.end(),
			std::inserter(c, c.begin())
		);
		return c.size() > s;
	}

public:
	/**
	 * Determines the set of variables that may be eliminated from a formula, given the set of all variables that occur in this formula.
	 * A variable can be eliminated, if no other differently quantified of a deeper level variable occurs.
	 * Returns the type of quantification of the eliminable variables.
     * @param variables Set of variables of the formula.
     * @param eliminable Set of eliminable variables.
     * @return Type of quantification. Can only be EXISTS or FORALL.
     */
	Type eliminable(const std::set<carl::Variable>& variables, std::set<carl::Variable>& eliminable) const {
		// Start with an empty set.
		eliminable.clear();
		// Iterate over all levels, starting with the deepest one.
		// Note that lvl counts from one so that we can use an unsigned type and safely decrement at the same time.
		for (size_t lvl = mData.size(); lvl > 0; lvl--) {
			// Check if any of the variables occurs at this level.
			if (intersect(mData[lvl-1], variables, eliminable)) {
				// If none of the variables occurs at the following level, we do not need to consider this one.
				std::set<carl::Variable> tmp;
				for (; lvl > 2; lvl -= 2) {
					// Check if any of the variables occurs at the following level.
					if (intersect(mData[lvl-2], variables, tmp)) {
						// If so, return.
						return (lvl % 2 == 1) ? Type::EXISTS : Type::FORALL;
					}
					// We can also include the next level.
					intersect(mData[lvl-3], variables, eliminable);
				}
			}
		}
		// If the variables did not occur at all, we just return anything.
		return Type::EXISTS;
	}

	/**
	 * Adds a variable that was has not been quantified explicitly.
	 * Such a variable is assumed to be quantified existentially.
	 * @param v Variable to add.
	 */
	void addUnquantifiedVariable(const carl::Variable& v) {
		if (mData.empty()) mData.emplace_back();
		mData.front().insert(v);
	}

	const QuantifiedVariables& quantifiers() const {
		return mData;
	}

	QuantifiedVariables& quantifiers() {
		return mData;
	}
};

}