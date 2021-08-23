#include "CoveringUtils.h"

namespace smtrat {

std::ostream& operator<<(std::ostream& os, const CellInformation& data) {
	if (data.mLowerBound && data.mUpperBound) {
		if (data.mLowerBound.value() == data.mUpperBound.value()) {
			return os << "[ " << data.mLowerBound.value() << ", " << data.mUpperBound.value() << "]";
		}
		return os << "( " << data.mLowerBound.value() << ", " << data.mUpperBound.value() << ")";
	}
	if (!data.mLowerBound && data.mUpperBound) {
		return os << "(-oo, " << data.mUpperBound.value() << ")";
	}
	if (data.mLowerBound && !data.mUpperBound) {
		return os << "( " << data.mLowerBound.value() << ", oo)";
	}
	return os << "(-oo, oo)";
}

//Should encode inequalities of 4.4.1
//Todo: refactor 
bool operator<=(const CellInformation& lhs, const CellInformation& rhs) {
	//1. lhs.lower-bound is -infty -> mLowerBound is not set
	// -> Return true if rhs.lower-bound is finite
	// -> Return true if lhs.upper-bound <= rhs.upper-bound
	if (!lhs.mLowerBound) {
		if (rhs.mLowerBound) return true;
		if (!lhs.mUpperBound) { // u1 = infty
			return !rhs.mUpperBound.has_value();
		} else if (!rhs.mUpperBound) { // u2 = infty
			return lhs.mUpperBound.has_value();
		} else if (lhs.mUpperBound <= rhs.mUpperBound) { //u1 and u2 finite
			return true;
		}
	}
	//2. lhs.lower-bound is finite and rhs.lower-bound is -infty -> return false
	if (!rhs.mLowerBound) return false;

	//3. both lower bounds are finite
	if (lhs.mLowerBound <= rhs.mLowerBound) {
		if (lhs.mLowerBound < rhs.mLowerBound) return true;

		if (!lhs.mUpperBound) { // u1 = infty
			return !rhs.mUpperBound.has_value();
		} else if (!rhs.mUpperBound) { // u2 = infty
			return lhs.mUpperBound.has_value();
		} else if (lhs.mUpperBound <= rhs.mUpperBound) { //u1 and u2 finite
			return true;
		}
	}
	return false;
}

//Todo: Dont forget to resprect bound types once they are used 
bool isInsideOf(const CellInformation& lhs, const CellInformation& rhs) {
	//assert(lhs <= rhs) ;
	SMTRAT_LOG_DEBUG("smtrat.covering", "Is " << rhs << " inside of " << lhs);

	if (lhs.mLowerBound) {
		if (!rhs.mLowerBound) return false;
		if (lhs.mLowerBound.value() > rhs.mLowerBound.value()) return false;
	}
	if (rhs.mUpperBound) {
		if (!lhs.mUpperBound) return false;
		if (lhs.mUpperBound.value() < rhs.mUpperBound.value()) return false;
	}
	return true;
}

void orderAndCleanIntervals(std::vector<CellInformation>& cells) {

	if (cells.size() <= 1) return;

	std::sort(cells.begin(), cells.end(), [](const CellInformation& lhs, const CellInformation& rhs) {
		return lhs <= rhs;
	});

	//todo remove redundancy of first kind
}

bool disjoint(const CellInformation& lhs, const CellInformation& rhs) {
	//assumes lhs <= rhs
	return lhs.mUpperBound.value() < rhs.mLowerBound.value();
}

bool sampleOutside(std::vector<CellInformation>& cells, RAN& sample) {
	orderAndCleanIntervals(cells);
	if (cells.empty()) {
		sample = RAN(0);
		return true;
	}
	//if lowest lower_bound is not -infty take sufficiently small number as sample
	if (cells[0].mLowerBound) {
		sample = carl::sample_below(cells[0].mLowerBound.value());
		return true;
	}
	//if highest upper_bound is not -infty take sufficiently large number as sample
	if (cells.back().mUpperBound) {
		sample = carl::sample_below(cells.back().mUpperBound.value());
		return true;
	}
	//Search for 2 adjacent cells which are disjoint, take a point between
	for (std::size_t i = 0; i < cells.size() - 1; i++) {
		if (disjoint(cells[i], cells[i + 1])) {
			sample = carl::sample_between(cells[i].mUpperBound.value(), cells[i + 1].mLowerBound.value());
			return true;
		}
	}

	//No sample was found, the cells cover the whole number line
	return false;
}

} // namespace smtrat
