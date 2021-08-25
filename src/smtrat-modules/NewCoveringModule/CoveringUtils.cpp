#include "CoveringUtils.h"

namespace smtrat {

//Operators for Cellbounds ;

std::ostream& operator<<(std::ostream& os, const LowerBound& data) {
	if (!data.number) {
		return os << "(-∞, ";
	}
	if (data.isOpen) {
		return os << "( " << data.number.value() << ", ";
	}
	return os << "[ " << data.number.value() << ", ";
}

std::ostream& operator<<(std::ostream& os, const UpperBound& data) {
	if (!data.number) {
		return os << "∞)";
	}
	if (data.isOpen) {
		return os << data.number.value() << ")";
	}
	return os << data.number.value() << "]";
}

bool operator<(const LowerBound& lhs, const LowerBound& rhs) {
	if (!rhs.number) return false; // rhs is -infty
	if (!lhs.number) return true;  // lhs is -infty
	if (lhs.isOpen) {
		return lhs.number.value() < rhs.number.value();
	} else {
		if (lhs.number.value() < rhs.number.value()) return true;
		return rhs.isOpen && lhs.number.value() == rhs.number.value();
	}
}

bool operator<=(const LowerBound& lhs, const LowerBound& rhs) {
	return !(rhs < lhs);
}

bool operator<(const UpperBound& lhs, const UpperBound& rhs) {
	if (!lhs.number) return false; //lhs is infty
	if (!rhs.number) return true;  //rhs is infty
	if (rhs.isOpen) {
		return lhs.number.value() < rhs.number.value();
	} else {
		if (lhs.number.value() < rhs.number.value()) return true;
		return lhs.isOpen && lhs.number.value() == rhs.number.value();
	}
}

bool operator<=(const UpperBound& lhs, const UpperBound& rhs) {
	return !(rhs < lhs);
}

bool operator<(const UpperBound& lhs, const LowerBound& rhs){
	if(!lhs.number) return false ; //lhs is infty
	if(!rhs.number) return false ; //rhs is infty
	if(lhs.isOpen || rhs.isOpen) return lhs.number.value() <= rhs.number.value() ;
	return lhs.number.value() < rhs.number.value() ; 
}


std::ostream& operator<<(std::ostream& os, const CellInformation& data) {
	return os << data.mLowerBound << "  " << data.mUpperBound;
}

//encode inequalities of 4.4.1
bool operator<=(const CellInformation& lhs, const CellInformation& rhs) {
	//First check
	return lhs.mLowerBound <= rhs.mLowerBound && (lhs.mLowerBound < rhs.mLowerBound || lhs.mUpperBound <= rhs.mUpperBound); // 3.
																															//Todo what exactly do with 4.?
}

bool isInsideOf(const CellInformation& lhs, const CellInformation& rhs) {
	// if one bound is totally wrong, we can just return false
	if ((rhs.mLowerBound < lhs.mLowerBound && lhs.mLowerBound.number) ||
		(lhs.mUpperBound < rhs.mUpperBound && lhs.mUpperBound.number)) {
		return false;
	}
	// check the bounds
	bool lowerOk = lhs.mLowerBound < rhs.mLowerBound && rhs.mLowerBound.number;
	bool upperOk = rhs.mUpperBound < lhs.mUpperBound && rhs.mUpperBound.number;
	// if both are ok, return true
	if (lowerOk && upperOk) {
		return true;
	}

	// Note that from this point on at least one bound is equal
	// to our bounds but no bound is outside of our bounds
	// check the bound types
	bool lowerBoundTypesOk; // True iff lhs.mLowerBounds type is at least as "weak" as rhs.mLowerBound type
	if (!lhs.mLowerBound.number) {
		//lhs.mLowerBound is -infty
		lowerBoundTypesOk = true;
	} else if (!lhs.mLowerBound.isOpen) {
		//[lowerBound -> ok as long as rhs.mLowerBound is not infty
		lowerBoundTypesOk = rhs.mLowerBound.number.has_value();
	} else {
		//(lowerBound -> ok only if rhs.mLowerBound is also open
		lowerBoundTypesOk = rhs.mLowerBound.isOpen;
	}
	bool upperBoundTypesOk; // True iff lhs.mUpperBounds type is at least as "weak" as rhs.mUpperBound type
	if (!lhs.mUpperBound.number) {
		//lhs.mLowerBound is -infty
		upperBoundTypesOk = true;
	} else if (!lhs.mUpperBound.isOpen) {
		//[upperBound -> ok as long as rhs.mUpperBound is not infty
		upperBoundTypesOk = rhs.mUpperBound.number.has_value();
	} else {
		//(upperBound -> ok only if rhs.mUpperBound is also open
		upperBoundTypesOk = rhs.mUpperBound.isOpen;
	}

	// if upper bounds are ok and lower bound types are ok, return true
	if (upperOk && lowerBoundTypesOk) {
		return true;
	}
	// if lower bounds are ok and upper bound types are ok, return true
	if (lowerOk && upperBoundTypesOk) {
		return true;
	}
	// if both bound types are ok, return true
	if (lowerBoundTypesOk && upperBoundTypesOk) {
		return true;
	}
	// otherwise return false
	return false; // not less and not equal
}

void orderAndCleanIntervals(std::vector<CellInformation>& cells) {

	if (cells.size() <= 1) return;

	std::sort(cells.begin(), cells.end(), [](const CellInformation& lhs, const CellInformation& rhs) {
		return lhs <= rhs;
	});

	//todo testing...
	auto iter = cells.begin();
	auto next = ++iter;
	while (next != cells.end()) {
		if (isInsideOf(*iter, *next)) {
			next = cells.erase(next);
			//todo: is iter now invalidated?
		} else {
			++iter;
			++next;
		}
	}
}

bool disjoint(const CellInformation& lhs, const CellInformation& rhs) {
	return lhs.mUpperBound < rhs.mLowerBound || rhs.mUpperBound < lhs.mLowerBound; //TODO
}

bool sampleOutside(std::vector<CellInformation>& cells, RAN& sample) {
	orderAndCleanIntervals(cells);
	SMTRAT_LOG_DEBUG("smtrat.covering", "Sampling outside of: " << cells);
	if (cells.empty()) {
		SMTRAT_LOG_DEBUG("smtrat.covering", "Cells are empty -> Sample = 0");
		sample = RAN(0);
		return true;
	}
	//if lowest lower_bound is not -infty take sufficiently small number as sample
	if (cells[0].mLowerBound.number) {
		sample = carl::sample_below(cells[0].mLowerBound.number.value());
		SMTRAT_LOG_DEBUG("smtrat.covering", "Take sufficiently small value: " << sample);
		return true;
	}
	//if highest upper_bound is not -infty take sufficiently large number as sample
	if (cells.back().mUpperBound.number) {
		sample = carl::sample_above(cells.back().mUpperBound.number.value());
		SMTRAT_LOG_DEBUG("smtrat.covering", "Take sufficiently large value: " << sample);
		return true;
	}
	//Search for 2 adjacent cells which are disjoint, take a point between
	//we can skip the first and the last cell as there have infty as lower/upper bounds
	for (std::size_t i = 1; i < cells.size() - 2; i++) {
		if (disjoint(cells[i], cells[i + 1])) {
			sample = carl::sample_between(cells[i].mUpperBound.number.value(), cells[i + 1].mLowerBound.number.value());
			SMTRAT_LOG_DEBUG("smtrat.covering", "Found disjoint cells: " << cells[i] << " and " << cells[i + 1]);
			SMTRAT_LOG_DEBUG("smtrat.covering", "Found sample: " << sample);
			return true;
		}
	}

	SMTRAT_LOG_DEBUG("smtrat.covering", "No sample was found, the cells cover the whole number line");
	return false;
}

} // namespace smtrat
