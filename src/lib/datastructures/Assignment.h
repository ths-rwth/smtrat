/**
 * @file Assignment.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <map>
#include <boost/variant.hpp>
#include "../Formula.h"
#include "vs/SqrtEx.h"
#include "carl/core/RealAlgebraicNumber.h"

namespace smtrat {

    /**
     * This class represents some value that is assigned to some variable.
     * It is implemented as subclass of a boost::variant.
     * Possible value types are bool, vs::SqrtEx and carl::RealAlgebraicNumberPtr.
     */
    class Assignment: public boost::variant<bool, vs::SqrtEx, carl::RealAlgebraicNumberPtr<smtrat::Rational>> {
        /**
         * Base type we are deriving from.
         */
        typedef boost::variant<bool, vs::SqrtEx, carl::RealAlgebraicNumberPtr<smtrat::Rational>> Super;
        
    public:
        /**
         * Default constructor.
         */
        Assignment(): Super() {
        }

        /**
         * Initializes the Assignment from some valid type of the underlying variant.
         */
        template<typename T>
        Assignment(const T& t): Super(t) {
        }

        /**
         * Assign some value to the underlying variant.
         * @param t Some value.
         * @return *this.
         */
        template<typename T>
        Assignment& operator=(const T& t) {
            Super::operator=(t);
            return *this;
        }

        /**
         * Check if two Assignments are equal.
         * Two Assignments are considered equal, if both are either bool or not bool and their value is the same.
         * 
         * If both Assignments are not bools, the check may return false although they represent the same value.
         * If both are numbers in different representations, this comparison is only done as a "best effort".
         * 
         * @param a Another Assignment.
         * @return *this == a.
         */
        bool operator==(const Assignment& a) {
            // Handle bools
            if (this->isBool()) {
                return (a.isBool()) && (this->asBool() == a.asBool());
            } else if (a.isBool()) {
                return false;
            }

            // Handle numbers
            if (this->isSqrtEx()) {
                if (a.isSqrtEx()) {
                    return this->asSqrtEx() == a.asSqrtEx();
                } else if (a.isRAN()) {
                    return false;
                }
            } else if (this->isRAN()) {
                if (a.isSqrtEx()) {
                    return false;
                } else if (a.isRAN()) {
                    return std::equal_to<carl::RealAlgebraicNumberPtr<smtrat::Rational>>()(this->asRAN(), a.asRAN());
                }
            }
            return false;
        }

        /**
         * Checks if the stored value is a bool.
         * @return 
         */
        bool isBool() const {
            return this->type() == typeid(bool);
        }
        
        /**
         * Checks if the stored value is a vs::SqrtEx.
         * @return 
         */
        bool isSqrtEx() const {
            return this->type() == typeid(vs::SqrtEx);
        }
        
        /**
         * Checks if the stored value is a carl::RealAlgebraicNumberPtr.
         * @return 
         */
        bool isRAN() const {
            return this->type() == typeid(carl::RealAlgebraicNumberPtr<smtrat::Rational>);
        }

        /**
         * Returns the stored value as a boolean.
         * Asserts that it is in fact a boolean.
         * @return 
         */
        bool asBool() const {
            assert(this->isBool());
            return boost::get<bool>(*this);
        }
        
        /**
         * Returns the stored value as a vs::SqrtEx.
         * Asserts that it is in fact a vs::SqrtEx.
         * @return 
         */
        vs::SqrtEx asSqrtEx() const {
            assert(this->isSqrtEx());
            return boost::get<vs::SqrtEx>(*this);
        }
        
        /**
         * Returns the stored value as a carl::RealAlgebraicNumberPtr.
         * Asserts that it is in fact a carl::RealAlgebraicNumberPtr.
         * @return 
         */
        carl::RealAlgebraicNumberPtr<smtrat::Rational> asRAN() const {
            assert(this->isRAN());
            return boost::get<carl::RealAlgebraicNumberPtr<smtrat::Rational>>(*this);
        }
    };

    /// Data type for a assignment assigning a variable, represented as a string, a real algebraic number, represented as a string.
    typedef std::map<const carl::Variable, Assignment> Model;
    
    /**
     * Obtains all assignments which can be transformed to rationals and stores them in the passed map.
     * @param _model The model from which to obtain the rational assignments.
     * @param _rationalAssigns The map to store the rational assignments in.
     * @return true, if the entire model could be transformed to rational assignments. (not possible if, e.g., sqrt is contained)
     */
    bool getRationalAssignmentsFromModel( const Model& _model, EvalRationalMap& _rationalAssigns );
    
    
            
    /**
     * @param _assignment The assignment for which to check whether the given formula is satisfied by it.
     * @param _formula The formula to be satisfied.
     * @return 0, if this formula is violated by the given assignment;
     *         1, if this formula is satisfied by the given assignment;
     *         2, otherwise.
     */
    unsigned satisfies( const Model& _assignment, const Formula* _formula );
}