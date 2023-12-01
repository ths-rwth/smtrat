
#include "smtrat-coveringng/PrenexNormalForm.h"
#include "smtrat-modules/QuantifierCoveringModule/GatherVariablesSubformulas.h"
#include <carl-arith/core/Relation.h>
#include <carl-arith/ran/common/RealRoots.h>
#include <carl-formula/formula/FormulaContent.h>
#include <functional>
#include <gtest/gtest.h>
#include <smtrat-common/types.h>

#include <carl-logging/logging-internals.h>
#include <carl-logging/logging.h>
#include <smtrat-common/logging.h>

using smtrat::ConstraintT;
using smtrat::FormulaT;
using smtrat::Poly;

inline void enable_logging() {
	if (!carl::logging::logger().has("stdout")) {
		carl::logging::logger().configure("stdout", std::cout);
	}
	carl::logging::logger().filter("stdout")("smtrat.covering_ng", carl::logging::LogLevel::LVL_ALL);
}

TEST(smtratQuantifierCovering, TestIndependentSubformulas1){
	enable_logging();

	// Example: (exists x y).(x > 0 and y > 0)
	auto x = carl::fresh_real_variable("x");
	auto y = carl::fresh_real_variable("y");
	auto formula = FormulaT(carl::FormulaType::EXISTS, std::vector({x, y}), FormulaT(carl::FormulaType::AND, std::vector({FormulaT(Poly(x), carl::Relation::GREATER), FormulaT(Poly(y), carl::Relation::GREATER)})));

	//convert to prenex normal form:
	smtrat::covering_ng::util::PrenexNormalFormConverter walker(formula);
	auto [quantifiers, matrix] = walker.getResult();

	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Formula: " << formula);
	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Quantifiers: " << quantifiers);
	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Matrix: " << matrix);

	//find independent subformulas:
	smtrat::covering_ng::subformulas::find_independent_subformulas(matrix);
}