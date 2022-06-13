#pragma once

#include "../common.h"

namespace smtrat::cad::projection {

/// Checks whether a polynomial can safely be ignored.
inline bool canBeRemoved(const UPoly& p) {
	return carl::is_zero(p) || p.is_number();
}
/// Checks whether a polynomial can safely be forwarded to the next level.
inline bool canBeForwarded(std::size_t, const UPoly& p) {
	return carl::is_constant(p);
}

}