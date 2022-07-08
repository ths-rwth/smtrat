#pragma once

#include <vector>

#include <carl-arith/ran/ran.h>

namespace smtrat::mcsat::onecellcad {

/**
 * Represent a multidimensional point whose components are algebraic reals.
 * This class is just a thin wrapper around vector to have a clearer semantic
 * meaning.
 */
template<typename Number>
class RealAlgebraicPoint {
private:
	/**
	 * Numbers of this RealAlgebraicPoint.
	 */
	std::vector<carl::IntRepRealAlgebraicNumber<Number>> mNumbers;

public:
	/**
	 * Create an empty point of dimension 0.
	 */
	RealAlgebraicPoint() noexcept = default;

  /**
   * Convert from a vector using its numbers in the same order as components.
   */
	explicit RealAlgebraicPoint(const std::vector<carl::IntRepRealAlgebraicNumber<Number>>& v):
		mNumbers(v)
	{}

  /**
   * Convert from a vector using its numbers in the same order as components.
   */
	explicit RealAlgebraicPoint(std::vector<carl::IntRepRealAlgebraicNumber<Number>>&& v):
		mNumbers(std::move(v))
	{}

  /**
   * Convert from a list using its numbers in the same order as components.
   */
	explicit RealAlgebraicPoint(const std::list<carl::IntRepRealAlgebraicNumber<Number>>& v):
		mNumbers(v.begin(), v.end())
	{}

  /**
   * Convert from a initializer_list using its numbers in the same order as components.
   */
	RealAlgebraicPoint(const std::initializer_list<carl::IntRepRealAlgebraicNumber<Number>>& v):
		mNumbers(v.begin(), v.end())
	{}

  /**
   * Give the dimension/number of components of this point.
   */
	std::size_t dim() const {
		return mNumbers.size();
	}

  /**
   * Make a (lower dimensional) copy that contains only the first
   * 'componentCount'-many components.
   */
  RealAlgebraicPoint prefixPoint(size_t componentCount) const {
    assert(componentCount <= mNumbers.size());
    std::vector<carl::IntRepRealAlgebraicNumber<Number>> copy(
    	mNumbers.begin(), std::next(mNumbers.begin(), componentCount));
    return RealAlgebraicPoint(std::move(copy));
  }

  /**
   * Create a new point with another given component added at the end of this
   * point, thereby increasing its dimension by 1. The original point remains
   * untouched.
   */
	RealAlgebraicPoint conjoin(const carl::IntRepRealAlgebraicNumber<Number>& r) {
		RealAlgebraicPoint res = RealAlgebraicPoint(*this);
		res.mNumbers.push_back(r);
		return res;
	}
	
  /**
   * Retrieve the component of this point at the given index.
   */
	const carl::IntRepRealAlgebraicNumber<Number>& operator[](std::size_t index) const {
		assert(index < mNumbers.size());
		return mNumbers[index];
	}
	
  /**
   * Retrieve the component of this point at the given index.
   */
	carl::IntRepRealAlgebraicNumber<Number>& operator[](std::size_t index) {
		assert(index < mNumbers.size());
		return mNumbers[index];
	}
};

/**
 * Check if two RealAlgebraicPoints are equal.
 */
template<typename Number>
bool operator==(RealAlgebraicPoint<Number>& lhs, RealAlgebraicPoint<Number>& rhs) {
	if (lhs.dim() != rhs.dim()) return false;
	std::not_equal_to<Number> neq;
	for (std::size_t i = 0; i < lhs.dim(); ++i) {
		if (neq(lhs[i], rhs[i])) return false;
	}
	return true;
}

/**
 * Streaming operator for a RealAlgebraicPoint.
 */
template<typename Number>
std::ostream& operator<<(std::ostream& os, const RealAlgebraicPoint<Number>& r) {
	os << "(";
	for (std::size_t i = 0; i < r.dim(); ++i) {
		if (i > 0) os << ", ";
		os << r[i];
	}
	os << ")";
	return os;
}

}
