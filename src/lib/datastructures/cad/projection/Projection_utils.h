#pragma once

#include "../Common.h"

namespace smtrat::cad::projection {

/// Checks whether a polynomial can safely be ignored.
inline bool canBeRemoved(const UPoly& p) {
	return p.isZero() || p.isNumber();
}
/// Checks whether a polynomial can safely be forwarded to the next level.
inline bool canBeForwarded(std::size_t, const UPoly& p) {
	return p.isConstant();
}

}