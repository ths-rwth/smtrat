#pragma once

#include <boost/optional.hpp>
#include <boost/optional/optional_io.hpp>

#include <carl/formula/model/ran/RealAlgebraicNumber.h>
#include <carl/formula/model/ran/RealAlgebraicNumberEvaluation.h>
#include <carl/util/Bitset.h>
#include <carl/util/IDPool.h>

#include "../../Common.h"
#include <smtrat-cad/Settings.h>
#include "utils/DynamicPriorityQueue.h"
#include "utils/Origin.h"

namespace smtrat {
namespace cad {
	using Variables = std::vector<carl::Variable>;
	using UPoly = carl::UnivariatePolynomial<Poly>;
	using RAN = carl::RealAlgebraicNumber<Rational>;
	using SampleLiftedWith = carl::Bitset;
	using SampleRootOf = carl::Bitset;
	using ConstraintSelection = carl::Bitset;
	using OptionalPoly = boost::optional<const UPoly&>;
	using OptionalID = boost::optional<std::size_t>;
	using Assignment = std::map<carl::Variable, RAN>;
}
}
