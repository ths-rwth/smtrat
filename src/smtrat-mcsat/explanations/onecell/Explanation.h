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

struct LDBSettings : BaseSettings {
    // constexpr static auto cell_heuristic = cadcells::representation::BIGGEST_CELL;
    // constexpr static auto cell_heuristic = cadcells::representation::CHAIN_EQ;
    // constexpr static auto cell_heuristic = cadcells::representation::LOWEST_DEGREE_BARRIERS_EQ;
    constexpr static auto cell_heuristic = cadcells::representation::LOWEST_DEGREE_BARRIERS;
    constexpr static auto covering_heuristic = cadcells::representation::LDB_COVERING;
    // constexpr static auto covering_heuristic = cadcells::representation::CHAIN_COVERING;
    //constexpr static auto op = cadcells::operators::op::mccallum;
    constexpr static auto op = cadcells::operators::op::mccallum;
};

struct LDBpdelSettings : BaseSettings {
    constexpr static auto cell_heuristic = cadcells::representation::LOWEST_DEGREE_BARRIERS_PDEL;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_PDEL;
    constexpr static auto op = cadcells::operators::op::mccallum_pdel;
};

struct LDBFilteredAllSelectiveSettings : BaseSettings {
    constexpr static auto cell_heuristic = cadcells::representation::LOWEST_DEGREE_BARRIERS_FILTER;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_FILTER;
    constexpr static auto op = cadcells::operators::op::mccallum_filtered_onlyrat_ew;
};

struct BCSettings : BaseSettings {
    constexpr static auto cell_heuristic = cadcells::representation::BIGGEST_CELL;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING;
    constexpr static auto op = cadcells::operators::op::mccallum;
};

struct BCpdelSettings : BaseSettings {
    constexpr static auto cell_heuristic = cadcells::representation::BIGGEST_CELL_PDEL;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_PDEL;
    constexpr static auto op = cadcells::operators::op::mccallum_pdel;
};

struct BCFilteredSettings : BaseSettings {
    constexpr static auto cell_heuristic = cadcells::representation::BIGGEST_CELL_FILTER;
    constexpr static auto covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_FILTER;
    constexpr static auto op = cadcells::operators::op::mccallum_filtered;
};

struct BCApproximationSettings : BCSettings {
    constexpr static bool use_approximation = true;
    constexpr static auto cell_apx_heuristic = cadcells::representation::BIGGEST_CELL_APPROXIMATION;
};

struct DefaultSettings : LDBSettings { // current default
};

// TODO keep context and cache as long as variable ordering does not change. but we need to make a context extensible.

template<typename Settings = DefaultSettings>
struct Explanation {
	#ifdef SMTRAT_DEVOPTION_Statistics
		OCStatistics& mStatistics = statistics_get<OCStatistics>("mcsat-explanation-onecell");
	#endif

    std::optional<mcsat::Explanation> operator()(const mcsat::Bookkeeping& trail, carl::Variable var, const FormulasT& reason, bool) const {
        #ifdef SMTRAT_DEVOPTION_Statistics
            mStatistics.explanationCalled();
        #endif

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
        SMTRAT_STATISTICS_CALL(cadcells::statistics().set_max_level(ass.size()+1));

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
        #ifdef SMTRAT_DEVOPTION_Statistics
            SMTRAT_TIME_START(start);
        #endif
        auto result = onecell<Settings>(constr, context, ass);
        #ifdef SMTRAT_DEVOPTION_Statistics
            SMTRAT_TIME_FINISH(mStatistics.timer(), start);
        #endif

        if (!result) {
            SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Could not generate explanation");
            return std::nullopt;
        }
        else {
            #ifdef SMTRAT_DEVOPTION_Statistics
                mStatistics.explanationSuccess();
            #endif
            SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Got unsat cell " << result << " of constraints " << constr << " wrt " << vars << " and " << ass);
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
                return mcsat::Explanation(ClauseChain::from_formula(FormulaT(carl::FormulaType::OR, std::move(expl)), trail.model(), Settings::clause_chain_with_equivalences));
            }
        } 
    }
};

}