#pragma once

#include "../common.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class CADInterval {
    public: 
        /** bound types for CAD interval bounds */
        enum CADBoundType {
            INF,
            OPEN,
            CLOSED
        };
	private:
        RAN lower;  /**< lower bound */
        RAN upper;  /**< upper bound */
        CADBoundType lowertype;    /**< lower bound type */
        CADBoundType uppertype;    /**< upper bound type */
	public:
        /** initializes interval as (-inf, +inf) */
		CADInterval(){
            lower = 0;
            upper = 0;
            lowertype = INF;
            uppertype = INF;
		}

        /** initializes closed interval with given bounds */
        CADInterval(RAN lowerbound, RAN upperbound): lower(lowerbound), upper(upperbound) {
            lowertype = CLOSED;
            uppertype = CLOSED;
        }

        /** initializes interval with given bounds and bound types */
        CADInterval(RAN lowerbound, RAN upperbound, CADBoundType lowerboundtype, CADBoundType upperboundtype):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype) {
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
