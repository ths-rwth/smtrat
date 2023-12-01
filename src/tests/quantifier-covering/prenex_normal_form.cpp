
#include "smtrat-coveringng/PrenexNormalForm.h"
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

inline FormulaT build_formula(const std::vector<smtrat::covering_ng::QuantifiedVariables>& quantifiers, FormulaT matrix) {
	// build a FormulaT object from the prenexed formula
	for (const auto& quantifier : quantifiers) {
		std::vector<carl::Variable> variables;
		for (const auto& variable : quantifier.getVariables()) {
			variables.emplace_back(variable);
		}
		FormulaT tmp = FormulaT(quantifier.getType(), variables, matrix);
		matrix = std::move(tmp);
	}
	return matrix;
}

TEST(smtratQuantifierCovering, testNegation) {
	//enable_logging();

	// Example: not (forall x. exists y. x - y > 0) -> exists x. forall y. x - y <= 0
	auto x = carl::fresh_real_variable("x");
	auto y = carl::fresh_real_variable("y");
	auto formula = FormulaT(carl::FormulaType::NOT, FormulaT(carl::FormulaType::FORALL, std::vector({x}), FormulaT(carl::FormulaType::EXISTS, std::vector({y}), FormulaT(Poly(x) - Poly(y), carl::Relation::GREATER))));
	auto prenexed = FormulaT(carl::FormulaType::EXISTS, std::vector({x}), FormulaT(carl::FormulaType::FORALL, std::vector({y}), FormulaT(Poly(x) - Poly(y), carl::Relation::LEQ)));

	smtrat::covering_ng::util::PrenexNormalFormConverter walker(formula);
	auto [quantifiers, matrix] = walker.getResult();

	auto prenex = build_formula(quantifiers, matrix);

	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Formula: " << formula);
	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Prenexed: " << prenex);

	// Compare the hashes of the prenexed formula and the formula we expect
	EXPECT_EQ(matrix.hash(), prenexed.hash());
}

TEST(smtratQuantifierCovering, testAndOr) {
	//enable_logging();

	// Example: (forall x. x > 0) and (exists x. x < 0) -> (forall x. x > 0) and (exists y. y < 0) with y != x
	auto x = carl::fresh_real_variable("x");
	auto formula = FormulaT(carl::FormulaType::AND, {FormulaT(carl::FormulaType::FORALL, std::vector({x}), FormulaT(Poly(x), carl::Relation::GREATER)), FormulaT(carl::FormulaType::EXISTS, std::vector({x}), FormulaT(Poly(x), carl::Relation::LESS))});

	smtrat::covering_ng::util::PrenexNormalFormConverter walker(formula);
	auto [quantifiers, matrix] = walker.getResult();

	auto prenex = build_formula(quantifiers, matrix);

	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Formula: " << formula);
	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Prenexed: " << prenex);

	EXPECT_EQ(formula.variables().size(), 1);
	EXPECT_EQ(prenex.variables().size(), 2);
}


TEST(smtratQuantifierCovering, testImplication){
	enable_logging();

	// Example: (forall x. x - 1 > 0) -> (exists x. x < 0)
	auto x = carl::fresh_real_variable("x");
	auto formula = FormulaT(carl::FormulaType::IMPLIES, {FormulaT(carl::FormulaType::FORALL, std::vector({x}), FormulaT(Poly(x)-Poly(1), carl::Relation::GREATER)), FormulaT(carl::FormulaType::EXISTS, std::vector({x}), FormulaT(Poly(x), carl::Relation::LESS))});

	smtrat::covering_ng::util::PrenexNormalFormConverter walker(formula);
	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "DAG: " << walker);
	auto [quantifiers, matrix] = walker.getResult();

	auto prenex = build_formula(quantifiers, matrix);

	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Formula: " << formula);
	SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Prenexed: " << prenex);

	EXPECT_EQ(formula.variables().size(), 1);
	EXPECT_EQ(prenex.variables().size(), 2);

}