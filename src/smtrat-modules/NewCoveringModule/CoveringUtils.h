#pragma once

#include <optional>

#include <carl/ran/ran.h>

#include "PolyRefVector.h"

namespace smtrat {

//RAN, with rational coefficients
using RAN = carl::RealAlgebraicNumber<mpq_class>;


//Todo: add bound types -> maybe use carl::Interval 
//Todo: carl::Interval can not have RAN as bounds?
struct CellInformation {
	//If not set, infinite is assumed
	std::optional<RAN> mLowerBound;
	std::optional<RAN> mUpperBound;

	//Polynomials in main variable (corresponds to the level in the variable ordering)
	PolyRefVector mMainPolys;

	//Polynomials in lowerVariables
	PolyRefVector mBottomPolys;

	//Polynomials characterizing the lower bound
	PolyRefVector mLowerPolys;

	//Polynomials characterizing the upper bound
	PolyRefVector mUpperPolys;	
};

//Todo: not really necessary as mProjections also stores a copy of mPool -> simplify
struct Helpers {
	//Cache for Polynomials (the constraints) - Variable Ordering must be known before init
	std::shared_ptr<smtrat::cadcells::datastructures::PolyPool> mPool;

	//Cache for polynomial computations
	std::shared_ptr<smtrat::cadcells::datastructures::Projections> mProjections;
};

std::ostream& operator<<(std::ostream& os, const CellInformation& data);

//Compare by Bounds according to 4.4.1
bool operator<=(const CellInformation& lhs, const CellInformation& rhs);

//Todo: Respect bound types once they are implemented
bool disjoint(const CellInformation& lhs, const CellInformation& rhs);

//Assumes lhs < rhs
bool isInsideOf(const CellInformation& lhs, const CellInformation& rhs);

//Order cells according to section 4.4.1
//Remove redundancy of first type
void orderAndCleanIntervals(std::vector<CellInformation>& cells);

//stores the sample in the given RAN reference
//Returns whether a sample was found or if the cells cover the whole number line
bool sampleOutside(std::vector<CellInformation>& cells, RAN& sample);

} // namespace smtrat
