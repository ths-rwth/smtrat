#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>
#include "OCStatistics.h"

#include "onecell.h"

#include <carl-formula/formula/functions/Negations.h>
#include <carl-arith/ran/Conversion.h>
#include <carl-arith/poly/Conversion.h>
#include <carl-arith/constraint/Conversion.h>
#include <carl-arith/extended/Conversion.h>

#include "../../utils/RootExpr.h"


namespace smtrat::mcsat::onecell {

struct BaseSettings {
    static constexpr bool clause_chain_with_equivalences = false;
	static constexpr bool enforce_tarski = false;

    constexpr static bool use_approximation = false;

    constexpr static bool exploit_strict_constraints = true;
};

struct DefaultSettings : BaseSettings { // current default
    constexpr static bool exploit_strict_constraints = true;

    using cell_heuristic = cadcells::representation::cell_heuristics::LowestDegreeBarriersCacheGlobalFilter;
    using covering_heuristic = cadcells::representation::covering_heuristics::LDBCoveringCacheGlobalFilter;

    struct OpSettings : cadcells::operators::MccallumFilteredCompleteSettings {
		static constexpr DelineationFunction delineation_function = BOUNDS_ONLY;
		static constexpr bool enable_weak = true;
	};
    using op = cadcells::operators::MccallumFiltered<cadcells::operators::MccallumFilteredCompleteSettings>;
};

struct DefaultApxSettings : DefaultSettings {
    constexpr static bool use_approximation = true;
    struct ApxSettings {
        using method = cadcells::representation::approximation::Simple<cadcells::representation::approximation::SimpleSettings>;
        struct CriteriaSettings : cadcells::representation::approximation::BaseCriteriaSettings {
            static constexpr std::size_t approximated_cells_limit = 100;
            static constexpr std::size_t single_degree_threshold  = 3;
            static constexpr std::size_t dynamic_degree_scale     = 2;
        };
        using Criteria = cadcells::representation::approximation::Criteria<CriteriaSettings>;
    };

    using Criteria = ApxSettings::Criteria;
	using cell_apx_heuristic = cadcells::representation::cell_heuristics::BiggestCellApproximation<ApxSettings>;
};

struct DefaultBCSettings : BaseSettings { // current default
    constexpr static bool exploit_strict_constraints = true;

    using cell_heuristic = cadcells::representation::cell_heuristics::BiggestCellFilter;
    using covering_heuristic = cadcells::representation::covering_heuristics::BiggestCellCoveringFilter;

    struct OpSettings : cadcells::operators::MccallumFilteredCompleteSettings {
		static constexpr DelineationFunction delineation_function = BOUNDS_ONLY;
		static constexpr bool enable_weak = true;
	};
    using op = cadcells::operators::MccallumFiltered<cadcells::operators::MccallumFilteredCompleteSettings>;
};

struct DefaultBCApxSettings : DefaultBCSettings {
    constexpr static bool use_approximation = true;
    struct ApxSettings {
        using method = cadcells::representation::approximation::Simple<cadcells::representation::approximation::SimpleSettings>;
        struct CriteriaSettings : cadcells::representation::approximation::BaseCriteriaSettings {
            static constexpr std::size_t approximated_cells_limit = 100;
            static constexpr std::size_t single_degree_threshold  = 3;
            static constexpr std::size_t dynamic_degree_scale     = 2;
        };
        using Criteria = cadcells::representation::approximation::Criteria<CriteriaSettings>;
    };

    using Criteria = ApxSettings::Criteria;
	using cell_apx_heuristic = cadcells::representation::cell_heuristics::BiggestCellApproximation<ApxSettings>;
};

// TODO keep context and cache as long as variable ordering does not change. but we need to make a context extensible.

template<typename Settings = DefaultSettings>
struct Explanation {
    SMTRAT_STATISTICS_CALL(
        OCStatistics& mStatistics = statistics_get<OCStatistics>("mcsat-explanation-onecell")
    );

    std::optional<mcsat::Explanation> operator()(const mcsat::Bookkeeping& trail, carl::Variable var, const FormulasT& reason, bool) const {
        SMTRAT_STATISTICS_CALL(mStatistics.explanationCalled());

        cadcells::VariableOrdering vars = trail.assignedVariables();
        vars.push_back(var);

        cadcells::Polynomial::ContextType context(vars);

        cadcells::Assignment ass;
        for (const auto& [key, value] : trail.model()) {
            if (value.isRAN()) {
                ass.emplace(key.asVariable(), carl::convert<cadcells::RAN>(value.asRAN()));
            } else {
                assert(value.isRational());
                ass.emplace(key.asVariable(), cadcells::RAN(value.asRational()));
            }
        }

        SMTRAT_STATISTICS_CALL(mStatistics.assignment(ass));
        //SMTRAT_STATISTICS_CALL(cadcells::statistics().set_max_level(ass.size()+1));

        carl::carlVariables reason_vars;
        for (const auto& r : reason) carl::variables(r,reason_vars);
        for (const auto v : reason_vars) {
            if (ass.find(v) == ass.end() && v != var) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Conflict reasons are of higher level than the current one.");
                return std::nullopt;
            }
        }

        std::vector<cadcells::Atom> constr;
        for (const auto& r : reason) {
            if (r.type() == carl::FormulaType::CONSTRAINT) {
                constr.emplace_back(carl::convert<cadcells::Polynomial>(context, r.constraint().constr()));
            } else if (r.type() == carl::FormulaType::VARCOMPARE) {
                constr.emplace_back(carl::convert<cadcells::Polynomial>(context, r.variable_comparison()));
            }
        }
        SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Explain conflict " << constr << " with " << vars << " and " << ass);
        SMTRAT_STATISTICS_CALL(mStatistics.timer_start());
        auto result = onecell<Settings>(constr, context, ass);
        SMTRAT_STATISTICS_CALL(mStatistics.timer_finish());

        if (!result) {
            SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Could not generate explanation");
            return std::nullopt;
        }
        else {
            SMTRAT_STATISTICS_CALL(mStatistics.explanationSuccess());
            SMTRAT_LOG_DEBUG(
                "smtrat.mcsat.onecell",
                "Got unsat cell " << result << " of constraints " << constr << " wrt " << vars << " and " << ass
            );

            FormulasT expl;
            for (const auto& f : reason) {
                expl.push_back(f.negated());
            }
            bool is_clause = true;
            for (const auto& disjunction : *result) {
                std::vector<FormulaT> tmp;
                for (const auto& f : disjunction) {
                    if (std::holds_alternative<cadcells::Constraint>(f)) {
                        tmp.push_back(FormulaT(ConstraintT(carl::convert<Poly>(std::get<cadcells::Constraint>(f)))).negated());
                    } else if (std::holds_alternative<cadcells::VariableComparison>(f)) {
                        auto transf = constr_from_vc(std::get<cadcells::VariableComparison>(f), ass, Settings::enforce_tarski);
                        if (transf.empty()) {
                            tmp.push_back(FormulaT(carl::convert<Poly>(std::get<cadcells::VariableComparison>(f))).negated());
                        } else {
                            std::vector<FormulaT> tmp2;
                            for (const auto& c : transf) {
                                tmp2.push_back(FormulaT(ConstraintT(carl::convert<Poly>(c))).negated());
                            }
                            tmp.emplace_back(carl::FormulaType::OR, std::move(tmp2));
                        }
                    } else {
                        assert(false);
                    }
                }
                if (tmp.size() > 1) is_clause = false;
                expl.emplace_back(carl::FormulaType::AND, std::move(tmp));
            }
            if (is_clause) {
                return mcsat::Explanation(FormulaT(carl::FormulaType::OR, std::move(expl)));
            } else {
                return mcsat::Explanation(ClauseChain::from_formula(
                    FormulaT(carl::FormulaType::OR, std::move(expl)),
                    trail.model(),
                    Settings::clause_chain_with_equivalences
                ));
            }
        } 
    }
};

}