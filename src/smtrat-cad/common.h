#pragma once

#include <smtrat-common/smtrat-common.h>

#include <boost/optional.hpp>
#include <boost/optional/optional_io.hpp>

namespace smtrat {
namespace cad {
	using carl::operator<<;

	using ConstraintSelection = carl::Bitset;
	using OptionalID = boost::optional<std::size_t>;
	using RAN = carl::RealAlgebraicNumber<Rational>;
	using Assignment = std::map<carl::Variable, RAN>;
	using SampleLiftedWith = carl::Bitset;
	using SampleRootOf = carl::Bitset;
	using UPoly = carl::UnivariatePolynomial<Poly>;
}
}