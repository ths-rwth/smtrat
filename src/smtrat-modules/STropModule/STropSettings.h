/**
 * @file STropSettings.h
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2022-04-19
 * Created on 2017-09-13.
 */

#pragma once

namespace smtrat
{
	enum class SeparatorType {STRICT = 0, WEAK = 1};
	
	/// Take conjunctions incrementally, construct linear formulas for LRA solver
	struct STropSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "STropModule<STropSettings1>";
		/// Type of linear separating hyperplane to search for
		static constexpr SeparatorType separatorType = SeparatorType::STRICT;
		/// Transform formula first (if false, make sure that this module is the backend of the SAT module)
		static constexpr bool transformationOn = false;
		/// Alternative transformation proposed by Jasper, currently no explicit name given.
		static constexpr bool jasperTransformation = false;
	};

	/* Transform formula into equivalent equation
	*  Sum up coefficients, if sum is less than 0 then find positive point (using reduction).
	*  if sum is greater than 0 find negative point (using reduction).
	*  Otherwise (x_1,...,x_n) = (1,...,1) is a solution
	*/
	struct STropSettings2
	{
		/// Name of the Module
		static constexpr auto moduleName = "STropModule<STropSettings2>";
		/// Type of linear separating hyperplane to search for
		static constexpr SeparatorType separatorType = SeparatorType::STRICT;
		/// Transform formula first (if false, make sure that this module is the backend of the SAT module)
		static constexpr bool transformationOn = true;
		/// Alternative transformation proposed by Jasper, currently no explicit name given.
		static constexpr bool jasperTransformation = false;
	};

	/// Transform to NNF then replace each constraint with its linear formula (equations become FALSE). Then let LRA solver solve.
	struct STropSettings3
	{
		/// Name of the Module
		static constexpr auto moduleName = "STropModule<STropSettings3>";
		/// Type of linear separating hyperplane to search for
		static constexpr SeparatorType separatorType = SeparatorType::STRICT;
		/// Transform formula first (if false, make sure that this module is the backend of the SAT module)
		static constexpr bool transformationOn = false;
		/// Alternative transformation proposed by Jasper, currently no explicit name given.
		static constexpr bool jasperTransformation = true;
	};
}
