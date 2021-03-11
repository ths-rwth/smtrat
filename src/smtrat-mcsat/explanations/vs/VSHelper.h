#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>
#include <carl/util/Common.h>
#include <carl-model/evaluation/ModelEvaluation.h>
#include <carl/vs/substitute.h>
#include <carl/vs/zeros.h>

#include <variant>
#include <vector>

namespace smtrat {
namespace mcsat {
namespace vs {
namespace helper {

    inline void getFormulaAtoms(const FormulaT& f, FormulaSetT& result) {
        if (f.getType() == carl::FormulaType::CONSTRAINT || f.getType() == carl::FormulaType::VARCOMPARE) {
            result.insert(f);
        } else if (f.getType() == carl::FormulaType::NOT) {
            getFormulaAtoms(f.subformula(), result);
        } else if (f.isNary()) {
            for (const auto& sub : f.subformulas()) {
                getFormulaAtoms(sub, result);
            }
        } else if (f.getType() == carl::FormulaType::TRUE || f.getType() == carl::FormulaType::FALSE) {
            result.insert(f);
        } else {
            assert(false);
        }
    }

    /**
     * Converts a DisjunctionOfConstraintConjunctions to a regular Formula.
     */
    inline FormulaT to_formula(const carl::vs::CaseDistinction<Poly>& docc) {
        FormulasT constraintConjunctions;
        for (const auto& conjunction : docc) {
            FormulasT constraintConjunction;
            for (const auto& constraint : conjunction) {
                constraintConjunction.emplace_back(constraint);
            }
            constraintConjunctions.emplace_back(carl::FormulaType::AND, std::move(constraintConjunction));
        }
        return FormulaT(carl::FormulaType::OR, std::move(constraintConjunctions));
    }

    /**
     * Get zeros with side conditions of the given constraint.
     * 
     * Kind of a generator function. Passes generated zeros to a callback function to avoid copying.
     */
    static bool generateZeros(const FormulaT& formula, const carl::Variable& eliminationVar, std::function<void(SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions)> yield_result) {
        std::vector<carl::vs::zero<Poly>> res;
        
        if (formula.getType()==carl::FormulaType::CONSTRAINT) {
            if (!carl::vs::gather_zeros(formula.constraint(), eliminationVar, res)) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate zero");
                return false;
            }
        } else if (formula.getType()==carl::FormulaType::TRUE || formula.getType()==carl::FormulaType::FALSE) {
            return true;
        } else if (formula.getType()==carl::FormulaType::VARCOMPARE) {
            if (!carl::vs::gather_zeros(formula.variableComparison(), eliminationVar, res)) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate zero");
                return false;
            }
        } else {
            assert(false);
            return false;
        }

        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Got zeros" << res);
        for (auto& z : res) {
            yield_result(std::move(z.sqrt_ex), std::move(z.side_condition));
        }
        return true;
    }
    
    struct TestCandidate {
        carl::vs::Term<Poly> term;
        ConstraintsT side_condition;
        bool operator==(const TestCandidate& other) const {
            return term == other.term && side_condition == other.side_condition;
        }
    };

    /**
     * Adds a new substitution to the given list of substitutions or merges it to an existing one.
     * Returns true if a new substitution was created.
     */
    static bool addOrMergeTestCandidate(std::vector<TestCandidate>& results, const TestCandidate& newSubstitution) {
        if(!(std::find(results.begin(), results.end(), newSubstitution) != results.end())) {
            results.push_back(newSubstitution);
            return true;
        }
        return false;
    }

    /**
     * Generate all test candidates according to "vanilla" virtual substitution.
     * Returns false iff VS is not applicable.
     */
    static bool generateTestCandidates( std::vector<TestCandidate>& results, const carl::Variable& eliminationVar, const FormulaSetT& constraints) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generating test candidates for " << constraints << " and variable " << eliminationVar);
        
        // add minus infinity
        TestCandidate minf = {carl::vs::Term<Poly>::minus_infty(), ConstraintsT()};
        results.emplace_back(minf);

        // scan through conditions for test candidates
        for (const auto& constraint : constraints) {
            // Determine the substitution type: normal or +epsilon
            assert(constraint.getType() == carl::FormulaType::CONSTRAINT || constraint.getType() == carl::FormulaType::TRUE || constraint.getType() == carl::FormulaType::FALSE || constraint.getType() == carl::FormulaType::VARCOMPARE);
            bool isConstraint = constraint.getType() == carl::FormulaType::CONSTRAINT || constraint.getType() == carl::FormulaType::TRUE || constraint.getType() == carl::FormulaType::FALSE;
            const carl::Relation& relation = isConstraint ? constraint.constraint().relation() : constraint.variableComparison().relation();
            bool weakConstraint = (relation == carl::Relation::EQ || relation == carl::Relation::LEQ || relation == carl::Relation::GEQ);
            auto subType = weakConstraint ? carl::vs::TermType::NORMAL : carl::vs::TermType::PLUS_EPSILON;

            // generate Zeros
            bool res = generateZeros(constraint, eliminationVar, [&](SqrtEx&& sqrtExpression, ConstraintsT&& sideConditions) {
                TestCandidate sub({carl::vs::Term<Poly>(subType, sqrtExpression), std::move(sideConditions)});
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generated test candidate " << sub.term);
                addOrMergeTestCandidate(results, sub);
            });

            if (!res) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate zeros of " << eliminationVar << " in " << constraint);
                return false;
            }
        }

        SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Generated test candidates successfully");
        return true;
    }

    inline bool substitute(const FormulaT& constr, const carl::Variable var, const carl::vs::Term<Poly>& term, FormulaT& result) {
        if (constr.getType() == carl::FormulaType::CONSTRAINT) {
            auto subres = carl::vs::substitute(constr.constraint(), var, term);
            if (!subres) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution failed");
                return false;
            } else {
                result = helper::to_formula(*subres);
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution obtained " << result);
                return true;
            }
        } else if (constr.getType() == carl::FormulaType::VARCOMPARE) {
            auto subres = carl::vs::substitute(constr.variableComparison(), var, term);
            if (!subres) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution failed");
                return false;
            } else {
                if (std::holds_alternative<carl::vs::CaseDistinction<Poly>>(*subres)) {
                    result = helper::to_formula(std::get<carl::vs::CaseDistinction<Poly>>(*subres));
                } else {
                    result = FormulaT(std::get<carl::VariableComparison<Poly>>(*subres));
                }
                
                SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution obtained " << result);
                return true;
            }
        } else {
            SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Formula type " << constr.getType() << " not supported for substitution");
            return false;
        }
    }
}
}
}
}