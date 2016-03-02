#pragma once

#include <boost/optional.hpp>

#include <carl/core/RealAlgebraicNumber.h>

#include "../../Common.h"
#include "Settings.h"
#include "utils/Bitset.h"

namespace smtrat {
namespace cad {
	using Variables = std::vector<carl::Variable>;
	using UPoly = carl::UnivariatePolynomial<Poly>;
	using RAN = carl::RealAlgebraicNumber<Rational>;
	using SampleLiftedWith = Bitset;
	using SampleRootOf = Bitset;
	using OptionalPoly = boost::optional<const UPoly&>;
}
}
