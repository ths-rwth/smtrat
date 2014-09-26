/**
 * @file QuantifierManager.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#include <algorithm>
#include <set>

#include "../Common.h"
#include "../Formula.h"

#pragma once

namespace smtrat {

class QuantifierManager {
private:
    /// The quantified variables.
	QuantifiedVariables mData;

	/**
	 * Calculates the intersection of two sets a and b and checks if this intersection is not empty.
	 * The intersection is added to a given third set c.
     * @param a First set.
     * @param b Second set.
     * @param c Third set.
     * @return If intersection is not empty.
     */
	template<typename T, typename O1, typename O2, typename O3>
	bool intersect(const std::set<T, O1>& a, const std::set<T, O2>& b, std::set<T, O3>& c) const {
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
	Type eliminable(const Variables& variables, Variables& eliminable) const {
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

    /**
     * @return A constant reference to the quantified variables.
     */
	const QuantifiedVariables& quantifiers() const {
		return mData;
	}

    /**
     * @return A reference to the quantified variables.
     */
	QuantifiedVariables& quantifiers() {
		return mData;
	}

	/**
	 * Extends the given variable order (that may be empty) such that it includes all given variables.
	 * Variables with a higher quantifier level have a lower precedence and end up in the back of the resulting vector.
	 * Depending on rebuildOrder, the order is either rebuild completely or only extended. In the latter case, the order of the elements already in the order will not change and new variables are inserted.
	 * If necessary, a custom ordering can be given.
	 * If the given order does not comply to the partial order induced by the quantifier hierarchy, this method may exhibit undefined behaviour.
	 * @param vars Variables to add to the variable order.
	 * @param order Existing variable order that is to be extended.
	 * @param rebuildOrder Controls if the order shall be extended or rebuilt.
	 * @param ordering A custom ordering.
	 * @return New extended variable order.
	 */
	template<typename Ordering = std::less<carl::Variable>>
	std::vector<carl::Variable> extendVariableOrder(const Variables& vars, const std::vector<carl::Variable>& order, bool rebuildOrder = true, const Ordering& ordering = Ordering()) {
		std::vector<carl::Variable> result;
		auto orderIt = order.begin();
		std::set<carl::Variable, Ordering> v(ordering);
		// Iterate over all quantifier levels.
		for (auto curLvl: mData) {
			v.clear();
			// Select variables from this level.
			intersect(curLvl, vars, v);
			// Process variables from order that are in this level.
			while (orderIt != order.end() && curLvl.count(*orderIt) > 0) {
				// If rebuildOrder, just insert the variable into v.
				// Otherwise directly write it to the result and make sure it won't appear again.
				if (rebuildOrder) v.insert(*orderIt);
				else {
					result.push_back(*orderIt);
					v.erase(*orderIt);
				}
				orderIt++;
			}
			// Append new variables to the result.
			result.insert(result.end(), v.begin(), v.end());
		}
		return result;
	}
};

}