/**
 * @file Assignment.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <boost/variant.hpp>
#include "datastructures/vs/SqrtEx.h"
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

}