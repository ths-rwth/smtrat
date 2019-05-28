#pragma once

#include "../common.h"

namespace smtrat {
namespace cad {
	class CADInterval {
    public: 
        /** bound types for CAD interval bounds */
        enum CADBoundType {
            INF,        /**< infinity */
            OPEN,       /**< open but not infinitiy (does not include bound value) */
            CLOSED      /**< closed (does include bound value) */
        };
	private:
        RAN lower = (RAN) 0;                                            /**< lower bound */
        RAN upper = (RAN) 0;                                            /**< upper bound */
        CADBoundType lowertype = INF;                                   /**< lower bound type */
        CADBoundType uppertype = INF;                                   /**< upper bound type */
        std::optional<const ConstraintT&> constraint = std::nullopt;    /**< this interval represents the bounds of this constraint */
	public:
        /** initializes interval as (-inf, +inf) */
		CADInterval(){     
        }

        /** initializes open interval with given bounds */
        CADInterval(RAN lowerbound, RAN upperbound): 
            lower(lowerbound), upper(upperbound) {
            lowertype = OPEN;
            uppertype = OPEN;
        }

        /** initializes closed point interval */
        CADInterval(RAN point): 
            lower(point), upper(point) {
            lowertype = CLOSED;
            uppertype = CLOSED;
        }

        /** initializes closed point interval with constraint */
        CADInterval(RAN point, const ConstraintT& cons): 
            lower(point), upper(point), constraint(cons) {
            lowertype = CLOSED;
            uppertype = CLOSED;
        }

        /** initializes open interval with given bounds and constraint */
        CADInterval(RAN lowerbound, RAN upperbound, const ConstraintT& cons): 
            lower(lowerbound), upper(upperbound), constraint(cons) {
            lowertype = OPEN;
            uppertype = OPEN;
        }

        /** initializes interval with given bounds and bound types */
        CADInterval(RAN lowerbound, RAN upperbound, CADBoundType lowerboundtype, CADBoundType upperboundtype):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype) {
        }

        /** initializes interval with given bounds, bound types and constraint */
        CADInterval(RAN lowerbound, RAN upperbound, CADBoundType lowerboundtype, CADBoundType upperboundtype, const ConstraintT& cons):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype), constraint(cons) {
        }

        /** gets lower bound */
        auto getLower() {
            return lower;
        }

        /** gets lower bound type */
        auto getLowerBoundType() {
            return lowertype;
        }

        /** gets upper bound */
        auto getUpper() {
            return upper;
        }

        /** gets upper bound type */
        auto getUpperBoundType() {
            return uppertype;
        }

        /** gets constraint the interval originated from */
        auto getConstraint() {
            return constraint;
        }

        /** sets lower bound value and bound type */
        void setLowerBound(RAN value, CADBoundType type) {
            lower = value;
            lowertype = type;
        }

        /** sets lower bound value and bound type */
        void setUpperBound(RAN value, CADBoundType type) {
            upper = value;
            uppertype = type;
        }

        /** sets constraint */
        void setConstraint(const ConstraintT& cons) {
            constraint.emplace(cons);
        }

        /** checks whether the interval is (-inf, +inf) */
        bool isInfinite() {
            if(lowertype == INF && uppertype == INF) {
                return true;
            }
            return false;
        }

        /** checks whether one of the bounds is infinite */
        bool isHalfBounded() {
            if((lowertype == INF && !uppertype == INF) || 
                (!lowertype == INF && uppertype == INF)) {
                return true;
            }
            return false;
        }

        /** checks whether the interval contains the given value */
        bool contains(RAN val) {
            if((lowertype == INF || (lowertype == CLOSED && lower <= val) ||
                (lowertype == OPEN && lower < val)) &&
                (uppertype == INF || (uppertype == CLOSED && upper >= val) ||
                (uppertype == OPEN && upper > val))) {
                return true;
            }
            return false;
        }
	};
}
};
