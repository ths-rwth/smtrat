#pragma once

#include <smtrat-common/smtrat-common.h>

#include <optional>
#include <boost/optional/optional_io.hpp>

namespace smtrat {
namespace cad {
	using carl::operator<<;

	using ConstraintSelection = carl::Bitset;
	using OptionalID = std::optional<std::size_t>;
	using Assignment = std::map<carl::Variable, RAN>;
	using SampleLiftedWith = carl::Bitset;
	using SampleRootOf = carl::Bitset;
	using UPoly = carl::UnivariatePolynomial<Poly>;
}
}