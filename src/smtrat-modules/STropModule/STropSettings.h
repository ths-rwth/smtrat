/**
 * @file STropSettings.h
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2022-04-19
 * Created on 2017-09-13.
 */

#pragma once
#include "Subtropical.h"

namespace smtrat {
enum class Mode { INCREMENTAL_CONSTRAINTS,
				  TRANSFORM_EQUATION,
				  TRANSFORM_FORMULA,
				  TRANSFORM_FORMULA_ALT };

/// Take conjunctions incrementally, construct linear formulas for LRA solver
struct STropSettings1 {
	/// Name of the Module
	static constexpr auto moduleName = "STropModule<STropSettings1>";
	/// Type of linear separating hyperplane to search for
	static constexpr subtropical::SeparatorType separatorType = subtropical::SeparatorType::SEMIWEAK;
	/// incremental mode for SMT solving
	static constexpr Mode mode = Mode::INCREMENTAL_CONSTRAINTS;

	static constexpr bool output_only = false;
};

/* Transform formula into equivalent equation
 *  Sum up coefficients, if sum is less than 0 then find positive point (using reduction).
 *  if sum is greater than 0 find negative point (using reduction).
 *  Otherwise (x_1,...,x_n) = (1,...,1) is a solution
 */
struct STropSettings2 {
	/// Name of the Module
	static constexpr auto moduleName = "STropModule<STropSettings2>";
	/// Type of linear separating hyperplane to search for
	static constexpr subtropical::SeparatorType separatorType = subtropical::SeparatorType::SEMIWEAK;
	/// transformation of the formula to an equation
	static constexpr Mode mode = Mode::TRANSFORM_EQUATION;

	static constexpr bool output_only = false;
};

/// Transform to NNF then replace each constraint with its linear formula (equations become FALSE). Then let LRA solver solve.
struct STropSettings3 {
	/// Name of the Module
	static constexpr auto moduleName = "STropModule<STropSettings3>";
	/// Type of linear separating hyperplane to search for
	static constexpr subtropical::SeparatorType separatorType = subtropical::SeparatorType::SEMIWEAK;
	/// transformation of the formula to a linear formula, preserving the Boolean structure
	static constexpr Mode mode = Mode::TRANSFORM_FORMULA;

	static constexpr bool output_only = false;
};

/// Transform to NNF then replace each constraint with its linear formula (equations become FALSE). Then let LRA solver solve.
struct STropSettings3b {
	/// Name of the Module
	static constexpr auto moduleName = "STropModule<STropSettings3b>";
	/// Type of linear separating hyperplane to search for
	static constexpr subtropical::SeparatorType separatorType = subtropical::SeparatorType::SEMIWEAK;
	/// transformation of the formula to a linear formula, preserving the Boolean structure
	static constexpr Mode mode = Mode::TRANSFORM_FORMULA_ALT;

	static constexpr bool output_only = false;
};

struct STropSettings2OutputOnly {
	/// Name of the Module
	static constexpr auto moduleName = "STropModule<STropSettings2OutputOnly>";
	/// Type of linear separating hyperplane to search for
	static constexpr subtropical::SeparatorType separatorType = subtropical::SeparatorType::SEMIWEAK;
	/// transformation of the formula to an equation
	static constexpr Mode mode = Mode::TRANSFORM_EQUATION;

	static constexpr bool output_only = true;
};

struct STropSettings3OutputOnly {
	/// Name of the Module
	static constexpr auto moduleName = "STropModule<STropSettings3OutputOnly>";
	/// Type of linear separating hyperplane to search for
	static constexpr subtropical::SeparatorType separatorType = subtropical::SeparatorType::SEMIWEAK;
	/// transformation of the formula to a linear formula, preserving the Boolean structure
	static constexpr Mode mode = Mode::TRANSFORM_FORMULA;

	static constexpr bool output_only = true;
};

struct STropSettings3bOutputOnly {
	/// Name of the Module
	static constexpr auto moduleName = "STropModule<STropSettings3bOutputOnly>";
	/// Type of linear separating hyperplane to search for
	static constexpr subtropical::SeparatorType separatorType = subtropical::SeparatorType::SEMIWEAK;
	/// transformation of the formula to a linear formula, preserving the Boolean structure
	static constexpr Mode mode = Mode::TRANSFORM_FORMULA_ALT;

	static constexpr bool output_only = true;
};
} // namespace smtrat
