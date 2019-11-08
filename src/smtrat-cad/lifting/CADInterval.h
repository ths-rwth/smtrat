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
        RAN lower = (RAN) 0;            /**< lower bound */
        RAN upper = (RAN) 0;            /**< upper bound */
        CADBoundType lowertype = INF;   /**< lower bound type */
        CADBoundType uppertype = INF;   /**< upper bound type */
        std::set<Poly> lowerreason;     /**< collection of polynomials for lower bound */
        std::set<Poly> upperreason;     /**< collection of polynomials for upper bound */
        std::set<smtrat::Poly> polys = std::set<smtrat::Poly>();         /**< interval represents the bounds computed from these polynoms (containing x_i) */
        std::set<smtrat::Poly> lowerpolys = std::set<smtrat::Poly>();  /**< polynoms not containing main variable x_i */

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

        /** initializes closed point interval with polynoms */
        CADInterval(RAN point, const std::set<Poly> newpoly): 
            lower(point), upper(point), polys(newpoly) {
            lowertype = CLOSED;
            uppertype = CLOSED;
        }

        /** initializes closed point interval with polynom */
        CADInterval(RAN point, const smtrat::Poly newpoly): 
            lower(point), upper(point) {
            lowertype = CLOSED;
            uppertype = CLOSED;
            polys.insert(newpoly);
        }

        /** initializes open interval with given bounds and polynoms */
        CADInterval(RAN lowerbound, RAN upperbound, const std::set<Poly> newpoly): 
            lower(lowerbound), upper(upperbound), polys(newpoly) {
            lowertype = OPEN;
            uppertype = OPEN;
        }

        /** initializes open interval with given bounds and polynom */
        CADInterval(RAN lowerbound, RAN upperbound, const smtrat::Poly newpoly): 
            lower(lowerbound), upper(upperbound){
            lowertype = OPEN;
            uppertype = OPEN;
            polys.insert(newpoly);
        }

        /** initializes (-inf, +inf) interval with given polynoms */
        CADInterval(const std::set<Poly> newpoly):
            polys(newpoly) {
        }

        /** initializes (-inf, +inf) interval with given polynom */
        CADInterval(const Poly newpoly) {
            polys.insert(newpoly);
        }

        /** initializes interval with given bounds and bound types */
        CADInterval(
            RAN lowerbound, 
            RAN upperbound, 
            CADBoundType lowerboundtype, 
            CADBoundType upperboundtype):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype) {
        }

        /** initializes interval with given bounds, bound types and polynoms */
        CADInterval(
            RAN lowerbound, 
            RAN upperbound, 
            CADBoundType lowerboundtype, 
            CADBoundType upperboundtype, 
            std::set<Poly> newpoly):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype), 
            polys(newpoly) {
        }

        /** initializes interval with given bounds, bound types and polynom */
        CADInterval(
            RAN lowerbound, 
            RAN upperbound, 
            CADBoundType lowerboundtype, 
            CADBoundType upperboundtype, 
            Poly newpoly):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype) {
            polys.insert(newpoly);
        }

        /** initializes interval with given bounds, bound types, reasons and polynoms */
        CADInterval(
            RAN lowerbound, 
            RAN upperbound, 
            CADBoundType lowerboundtype, 
            CADBoundType upperboundtype, 
            std::set<Poly> lowerres,
            std::set<Poly> upperres, 
            std::set<Poly> newpoly):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype), 
            lowerreason(lowerres), upperreason(upperres), polys(newpoly) {
        }

        /** initializes interval with given bounds, bound types, reasons and polynom */
        CADInterval(
            RAN lowerbound, 
            RAN upperbound, 
            CADBoundType lowerboundtype, 
            CADBoundType upperboundtype, 
            std::set<Poly> lowerres,
            std::set<Poly> upperres, 
            Poly newpoly):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype), 
            lowerreason(lowerres), upperreason(upperres){
            
            polys.insert(newpoly);
        }

        /** initializes interval with given bounds, bound types, reasons, polynom and polynom without leading term */
        CADInterval(
            RAN lowerbound, 
            RAN upperbound, 
            CADBoundType lowerboundtype, 
            CADBoundType upperboundtype, 
            std::set<Poly> lowerres, 
            std::set<Poly> upperres, 
            std::set<Poly> newpoly, 
            std::set<Poly> newredpoly):
            lower(lowerbound), upper(upperbound), lowertype(lowerboundtype), uppertype(upperboundtype),
            lowerreason(lowerres), upperreason(upperres), polys(newpoly), lowerpolys(newredpoly) {
        }

        /** gets lower bound */
        const auto& getLower() const {
            return lower;
        }

        /** gets lower bound type */
        auto getLowerBoundType() const {
            return lowertype;
        }

        /** gets upper bound */
        const auto& getUpper() const {
            return upper;
        }

        /** gets upper bound type */
        auto getUpperBoundType() const {
            return uppertype;
        }

        /** gets polynoms the lower bound is reasoned from */
        auto getLowerReason() {
            return lowerreason;
        }

        /** gets polynoms the upper bound is reasoned from */
        auto getUpperReason() {
            return upperreason;
        }

        /** gets polynoms the interval originated from */
        auto getPolynoms() {
            return polys;
        }

        /** gets the reduced polynom */
        auto getLowerPolynoms() {
            return lowerpolys;
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

        /** sets polynoms */
        void setPolynom(const smtrat::Poly newpoly) {
            polys.clear();
            polys.insert(newpoly);
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
            /* if this bound is inf (& the other one not), the other one is greater */
            if(lowertype == INF && inter.getLowerBoundType() != INF)
                return true;
            /* if other bound is inf, this one is not lower */
            if(inter.getLowerBoundType() == INF)
                return false;

            if(lower < inter.getLower())
                return true;
            // if equal let upper type decide
            if(lower == inter.getLower()) {
				if (uppertype == INF) return false;
				if (inter.getUpperBoundType() == INF) return true;
				if(upper <= inter.getUpper())
                    return true;
            }

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

std::ostream& operator<<(std::ostream& os, const CADInterval* i) {
	switch (i->getLowerBoundType()) {
		case CADInterval::CADBoundType::INF: os << "(-oo, "; break;
		case CADInterval::CADBoundType::CLOSED: os << "[" << i->getLower() << ", "; break;
		case CADInterval::CADBoundType::OPEN: os << "(" << i->getLower() << ", "; break;
	}
	switch (i->getUpperBoundType()) {
		case CADInterval::CADBoundType::INF: os << "oo)"; break;
		case CADInterval::CADBoundType::CLOSED: os << i->getUpper() << "]"; break;
		case CADInterval::CADBoundType::OPEN: os << i->getUpper() << ")"; break;
	}
	return os;
}

}   //cad
};  //smtrat
