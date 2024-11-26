#pragma once

#include "common.h"
#include "datastructures/roots.h"
#include "datastructures/polynomials.h"

#include <carl-arith/poly/Conversion.h>
#include <carl-arith/constraint/Conversion.h>
#include <carl-arith/extended/Conversion.h>

namespace smtrat::cadcells::helper {

/**
 * Converts an @ref datastructures::IndexedRoot to a @ref MultivariateRoot.
 */
inline MultivariateRoot as_multivariate_root(const datastructures::PolyPool& pool, carl::Variable main_var, datastructures::IndexedRoot r) {
    const Polynomial& poly = pool(r.poly);
    assert(carl::variables(poly).has(main_var));
    return MultivariateRoot(poly, r.index, main_var);
}

/**
 * Converts a @ref datastructures::SymbolicInterval to a @ref DNF.
 */
inline DNF to_formula(const datastructures::PolyPool& pool, carl::Variable main_var, const datastructures::SymbolicInterval& c) {
    DNF cnf;
    if (c.is_section()) {
        cnf.emplace_back();
        cnf.back().emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.section_defining()), carl::Relation::EQ));
    } else {
        if (!c.lower().is_infty()) {
            auto rel = c.lower().is_strict() ? carl::Relation::GREATER : carl::Relation::GEQ;
            if (c.lower().value().is_root()) {
                cnf.emplace_back();
                cnf.back().emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.lower().value().root()), rel));
            } else {
                assert(c.lower().value().is_cmaxmin());
                for (const auto& rs : c.lower().value().cmaxmin().roots) {
                    cnf.emplace_back();
                    for (const auto& r : rs) {
                        cnf.back().emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,r), rel));
                    }
                }
            }
        }
        if (!c.upper().is_infty()) {
            auto rel = c.upper().is_strict() ? carl::Relation::LESS : carl::Relation::LEQ;
            if (c.upper().value().is_root()) {
                cnf.emplace_back();
                cnf.back().emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,c.upper().value().root()), rel));
            } else {
                assert(c.upper().value().is_cminmax());
                for (const auto& rs : c.upper().value().cminmax().roots) {
                    cnf.emplace_back();
                    for (const auto& r : rs) {
                        cnf.back().emplace_back(VariableComparison(main_var, as_multivariate_root(pool,main_var,r), rel));
                    }
                }
            }
        }
    } 
    return cnf;
}

inline FormulaT to_formula_carl(const cadcells::datastructures::PolyPool& pool, carl::Variable variable, const cadcells::datastructures::SymbolicInterval& interval) {
	auto dnf = cadcells::helper::to_formula(pool, variable, interval);
	FormulasT result;
	for (const auto& disjunction : dnf) {
		std::vector<FormulaT> tmp;
		for (const auto& f : disjunction) {
			if (std::holds_alternative<cadcells::Constraint>(f)) {
				tmp.push_back(FormulaT(ConstraintT(carl::convert<Poly>(std::get<cadcells::Constraint>(f)))));
			} else if (std::holds_alternative<cadcells::VariableComparison>(f)) {
				auto constraint = carl::as_constraint(std::get<cadcells::VariableComparison>(f));
				if (!constraint) {
					tmp.push_back(FormulaT(carl::convert<Poly>(std::get<cadcells::VariableComparison>(f))));
				} else {
					tmp.push_back(FormulaT(ConstraintT(carl::convert<Poly>(*constraint))));
				}
			} else {
				assert(false);
			}
		}
		result.emplace_back(carl::FormulaType::OR, std::move(tmp));
	}
	return FormulaT(carl::FormulaType::AND, std::move(result));
}

}