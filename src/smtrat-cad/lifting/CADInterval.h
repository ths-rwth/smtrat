#pragma once

#include "../common.h"

#include <carl/formula/model/ran/RealAlgebraicNumberOperations.h>

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
        RAN lower = (RAN) 0;                        /**< lower bound */
        RAN upper = (RAN) 0;                        /**< upper bound */
        CADBoundType lowertype = INF;               /**< lower bound type */
        CADBoundType uppertype = INF;               /**< upper bound type */
        std::vector<Poly> lowerreason;              /**< collection of polynomials for lower bound */
        std::vector<Poly> upperreason;              /**< collection of polynomials for upper bound */
        smtrat::Poly poly = smtrat::Poly();         /**< interval represents the bounds computed from this polynom */
        smtrat::Poly reducedpoly = smtrat::Poly();  /**< polynom without leading term P_i */

    public:
        /** initializes interval as (-inf, +inf) */
		CADInterval(){}

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

        /** initializes closed point interval with polynom */
        CADInterval(RAN point, const smtrat::Poly newpoly): 
            lower(point), upper(point), poly(newpoly) {
            lowertype = CLOSED;
            uppertype = CLOSED;
        }

        /** initializes open interval with given bounds and polynom */
        CADInterval(RAN lowerbound, RAN upperbound, const smtrat::Poly newpoly): 
            lower(lowerbound), upper(upperbound), poly(newpoly) {
            lowertype = OPEN;
            uppertype = OPEN;
        }

        /** initializes (-inf, +inf) interval with given polynom */
        CADInterval(const smtrat::Poly newpoly):
            poly(newpoly) {
        }

        /** initializes interval with given bounds and bound types */
        CADInterval(
            RAN lowerbound, 
            RAN upperbound, 
            CADBoundType lowerboundtype, 
            CADBoundType upperboundtype):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype) {
        }

        /** initializes interval with given bounds, bound types and polynom */
        CADInterval(
            RAN lowerbound, 
            RAN upperbound, 
            CADBoundType lowerboundtype, 
            CADBoundType upperboundtype, 
            const smtrat::Poly newpoly):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype), 
            poly(newpoly) {
        }

        /** initializes interval with given bounds, bound types, reasons and polynom */
        CADInterval(
            RAN lowerbound, 
            RAN upperbound, 
            CADBoundType lowerboundtype, 
            CADBoundType upperboundtype, 
            std::vector<Poly> lowerres, 
            std::vector<Poly> upperres, 
            const smtrat::Poly newpoly):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype), 
            lowerreason(lowerres), upperreason(upperres), poly(newpoly) {
        }

        /** initializes interval with given bounds, bound types, reasons, polynom and polynom without leading term */
        CADInterval(
            RAN lowerbound, 
            RAN upperbound, 
            CADBoundType lowerboundtype, 
            CADBoundType upperboundtype, 
            std::vector<Poly> lowerres, 
            std::vector<Poly> upperres, 
            const smtrat::Poly newpoly, 
            const smtrat::Poly newredpoly):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype),
            lowerreason(lowerres), upperreason(upperres), poly(newpoly), reducedpoly(newredpoly) {
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

        /** gets polynom the interval originated from */
        auto getPolynom() {
            return poly;
        }

        /** gets the reduced polynom */
        auto getRedPoly() {
            return reducedpoly;
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

        /** sets polynom */
        void setPolynom(const smtrat::Poly newpoly) {
            poly = newpoly;
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

        /** @brief checks whether the lower bound is lower than the one of the given interval
         * 
         * @note can handle inf bounds
         * @returns true iff the lower bound is lower than the one of the given interval
         */
        bool isLowerThan(CADInterval inter) {
            /* if other bound is inf, this one is not lower */
            if(inter.getLowerBoundType() == INF)
                return false;
            /* if this bound is inf (& the other one not), the other one is greater */
            if(lowertype == INF)
                return true;

            if(lower < inter.getLower())
                return true;

            return false;
        }

        /** gets a value within the interval
         * @note if at least one bound is inf, some other value is given
        */
        RAN getRepresentative() {
            if(lowertype == INF && uppertype == INF)
                return (RAN) 0;

            if(lowertype == INF) {
                if(uppertype == CLOSED)
                    return upper;
                if(uppertype == OPEN)
                    return sampleBelow(upper);
            }
            
            if(uppertype == INF) {
                if(lowertype == CLOSED)
                    return lower;
                if(lowertype == OPEN)
                    return sampleAbove(lower);
            }
            
            if(lower == upper)
                return lower;

            return sampleBetween(lower, upper);
        }
	};
}   //cad
};  //smtrat
