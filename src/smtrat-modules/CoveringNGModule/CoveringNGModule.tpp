#include "CoveringNGModule.h"

#include <carl-arith/ran/Conversion.h>
#include <carl-formula/formula/functions/Substitution.h>
#include <smtrat-coveringng/Algorithm.h>
#include <smtrat-coveringng/VariableOrdering.h>

namespace smtrat {

template<class Settings>
CoveringNGModule<Settings>::CoveringNGModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager)
    : Module(_formula, _conditionals, _manager) {}

template<class Settings>
CoveringNGModule<Settings>::~CoveringNGModule() {}

template<class Settings>
bool CoveringNGModule<Settings>::informCore(const FormulaT&) { return true; }

template<class Settings>
bool CoveringNGModule<Settings>::addCore(ModuleInput::const_iterator) { return true; }

template<class Settings>
void CoveringNGModule<Settings>::removeCore(ModuleInput::const_iterator) {}

template<class Settings>
void CoveringNGModule<Settings>::updateModel() const {}

template<typename Settings>
Answer CoveringNGModule<Settings>::checkCore() {
    FormulaT input(rReceivedFormula());

    std::map<carl::Variable, carl::Variable> var_mapping;
    // for quantified problems, the following setting is mandatory for correctness:
    if constexpr (Settings::transform_boolean_variables_to_reals) {
        // this is a hack until we have proper Boolean reasoning
        std::map<FormulaT,FormulaT> substitutions;
        for (const auto b_var : carl::boolean_variables(input)) {
            auto r_var = carl::fresh_real_variable("r_"+b_var.name());
            var_mapping.emplace(r_var, b_var);
            auto constraint = FormulaT(ConstraintT(r_var, carl::Relation::GREATER));
            substitutions.emplace(FormulaT(b_var), constraint);
            //substitutions.emplace(FormulaT(b_var).negated(), constraint.negated());
        }
        input = carl::substitute(input, substitutions);
        assert(carl::boolean_variables(input).empty());
        SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Formula after replacing Boolean variables: " << input);
    }

    carl::QuantifierPrefix prefix;
    FormulaT matrix;
    if ((carl::PROP_CONTAINS_QUANTIFIER_EXISTS <= input.properties()) || 
        (carl::PROP_CONTAINS_QUANTIFIER_FORALL <= input.properties())
    ) {
        std::tie(prefix, matrix) = carl::to_pnf(input);
	    SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Got PNF: " << prefix << " " << matrix);
	    #ifdef SMTRAT_DEVOPTION_Validation
	    SMTRAT_VALIDATION_ADD(
            "smtrat.covering_ng", "pnf", 
            FormulaT(carl::FormulaType::IFF, input, carl::to_formula(prefix, matrix)).negated(), 
            false
        )
	    #endif
    } else {
        SMTRAT_LOG_DEBUG("smtrat.covering_ng", "Got QF formula: " << input);
        matrix = input;
    }

    covering_ng::VariableQuantification variable_quantification;
	for (const auto& q : prefix) {
		variable_quantification.set_var_type(q.second, q.first);
	}

	std::vector<carl::Variable> var_order = covering_ng::variables::get_variable_ordering<Settings::variable_ordering_heuristic>(prefix, matrix);

    // move objective variable to the front if it is an optimization problem
    // TODO: design specialized var ordering heuristic
    if (is_minimizing()) {
        auto it = std::find(var_order.begin(), var_order.end(), mObjectiveVariable);
        assert(it != var_order.end());
        std::rotate(var_order.begin(), it, it+1);

        if constexpr (Settings::minimize_by_qe) {
            // make all variables except target quantified
            for (std::size_t i = 1; i < var_order.size(); ++i) {
                if (!variable_quantification.has(var_order[i])) {
                    variable_quantification.set_var_type(var_order[i], carl::Quantifier::EXISTS);
                }
            }
        }
    }

    SMTRAT_STATISTICS_CALL(covering_ng::statistics().variable_ordering(var_order, var_mapping));
    SMTRAT_STATISTICS_CALL(cadcells::statistics().set_max_level(var_order.size()));

    cadcells::Polynomial::ContextType context(var_order);
    cadcells::datastructures::PolyPool pool(context);
    cadcells::datastructures::Projections proj(pool);

    cadcells::Assignment ass;
    auto f = Settings::formula_evaluation::create(proj);
    f.set_formula(matrix);
    f.extend_valuation(ass);
    if (f.root_valuation() == covering_ng::formula::Valuation::FALSE || matrix.is_false()) {
        mModel.clear();
        generateTrivialInfeasibleSubset();
        return Answer::UNSAT;
    } else if (f.root_valuation() == covering_ng::formula::Valuation::TRUE || matrix.is_true()) {
        mModel.clear();
        return is_minimizing() ? Answer::OPTIMAL : Answer::SAT;
    }
    
    if (is_minimizing()) {
        if constexpr (Settings::minimize_by_qe) {
            return minimize_by_qe(proj, f, ass, variable_quantification, var_order, var_mapping);
        } else {
            return minimize(proj, f, ass, variable_quantification, var_order, var_mapping);
        }
    } 

    auto res = covering_ng::recurse<typename Settings::op,
                                    typename Settings::formula_evaluation::Type,
                                    typename Settings::covering_heuristic,
                                    Settings::sampling_algorithm,
                                    typename Settings::cell_heuristic>
                                    (proj, f, ass, variable_quantification);

    if (res.is_sat()) {
        mModel.clear();
        if (res.sample()) {
            for (const auto& a : *res.sample()) {
                if constexpr (Settings::transform_boolean_variables_to_reals) {
                    auto var_mapping_it = var_mapping.find(a.first);
                    if (var_mapping_it != var_mapping.end()) {
                        mModel.emplace(var_mapping_it->second, a.second > 0);
                    } else {
                        mModel.emplace(a.first, carl::convert<smtrat::RAN>(a.second));
                    }
                } else {
                    mModel.emplace(a.first, carl::convert<smtrat::RAN>(a.second));
                }
            }
        }
        return Answer::SAT;
    } else {
        return process_result(res);
    }
}


template<typename Settings>
Answer CoveringNGModule<Settings>::minimize(cadcells::datastructures::Projections& proj,
                                            Settings::formula_evaluation::Type& f,
                                            cadcells::Assignment& ass,
                                            const covering_ng::VariableQuantification& variable_quantification,
                                            const std::vector<carl::Variable>& var_order,
                                            const std::map<carl::Variable, carl::Variable>& var_mapping) {

    auto [res, cell] = covering_ng::minimize<typename Settings::op,
                                             typename Settings::formula_evaluation::Type,
                                             typename Settings::covering_heuristic,
                                             Settings::sampling_algorithm,
                                             typename Settings::cell_heuristic>
                                             (proj, f, ass, variable_quantification);

    if (!res.is_optimal()) return process_result(res);

    mModel.clear();
    assert(res.sample());

    if (res.status == covering_ng::Status::OPT_CLOSED) {
        // res contains only the best interval
        const auto& r = res.intervals().front()->cell().lower()->first;
        mModel.emplace(mObjectiveVariable, carl::convert<RAN>(r));
        cadcells::Assignment ass;
        ass.emplace(mObjectiveVariable, r);

        // starting at 1 bc objectiveVariable is at 0
        for (std::size_t i = 1; i < cell.size(); ++i) {
            if constexpr (Settings::transform_boolean_variables_to_reals) {
                const auto& value = res.sample()->at(var_order[i]);
                auto var_mapping_it = var_mapping.find(var_order[i]);
                if (var_mapping_it != var_mapping.end()) {
                    mModel.emplace(var_mapping_it->second, value > 0);
                    continue;
                }
            }

            const auto& interval = cell[cell.size() - i - 1]; // cell is in reverse order

            if (interval.lower().is_infty()) {
                if (interval.upper().is_infty()) {
                    ass.emplace(var_order[i], 0);
                } else {
                    ass.emplace(var_order[i], carl::sample_below(proj.evaluate(ass, interval.upper().value().root())));
                }
            } else if (interval.upper().is_infty()) {
                ass.emplace(var_order[i], carl::sample_above(proj.evaluate(ass, interval.lower().value().root())));
            } else if (interval.is_section()) {
                ass.emplace(var_order[i], proj.evaluate(ass, interval.lower().value().root()));
            } else {
                ass.emplace(
                    var_order[i],
                    carl::sample_between(
                        proj.evaluate(ass, interval.lower().value().root()),
                        proj.evaluate(ass, interval.upper().value().root())
                    )
                );
            }

            mModel.emplace(var_order[i], carl::convert<RAN>(ass.at(var_order[i])));
        }
    } else {
        if (res.status == covering_ng::Status::OPT_UNBOUNDED) {
            mModel.emplace(mObjectiveVariable, carl::InfinityValue{});
        } else {
            assert(res.status == covering_ng::Status::OPT_OPEN);
            RAN l = carl::convert<RAN>(res.intervals().front()->cell().lower()->first);
            m_minimization_max_epsilon = Rational(1);
            if (!res.intervals().front()->cell().upper_unbounded()){
                RAN u = carl::convert<RAN>(res.intervals().front()->cell().upper()->first);
                Rational u_rat = (u.is_numeric() ? u.value() : u.interval().lower());
                Rational l_rat = (l.is_numeric() ? l.value() : l.interval().upper());
                m_minimization_max_epsilon = u_rat - l_rat;
            }
            carl::Variable eps = carl::fresh_real_variable("max_epsilon"); // TODO: hacky
            mModel.emplace(eps, m_minimization_max_epsilon);
            mModel.emplace(mObjectiveVariable, carl::Infinitesimal{l, true});
        }

        // starting at 1 bc objectiveVariable is at 0
        for (std::size_t i = 1; i < cell.size(); ++i) {
            if constexpr (Settings::transform_boolean_variables_to_reals) {
                const auto& value = res.sample()->at(var_order[i]);
                auto var_mapping_it = var_mapping.find(var_order[i]);
                if (var_mapping_it != var_mapping.end()) {
                    mModel.emplace(var_mapping_it->second, value > 0);
                    continue;
                }
            }

            carl::SymbolicInterval<Poly> sym_int;
            const auto& interval = cell[cell.size() - i - 1]; // cell is in reverse order

            if (!interval.lower().is_infty()) {
                const auto& ir_lower = interval.lower().value().root();
                sym_int.lower = MultivariateRootT(carl::convert<Poly>(proj.polys()(ir_lower.poly)), ir_lower.index, var_order[i]);
                sym_int.lower_strict = interval.lower().is_strict();
            }
            if (!interval.upper().is_infty()) {
                const auto& ir_upper = interval.upper().value().root();
                sym_int.upper = MultivariateRootT(carl::convert<Poly>(proj.polys()(ir_upper.poly)), ir_upper.index, var_order[i]);
                sym_int.upper_strict = interval.upper().is_strict();
            }
            mModel.emplace(var_order[i], sym_int);
        }
    }

    validation_minimize(Answer::OPTIMAL);
    return Answer::OPTIMAL;
}



template<typename Settings>
Answer CoveringNGModule<Settings>::minimize_by_qe(cadcells::datastructures::Projections& proj,
                                                  Settings::formula_evaluation::Type& f,
                                                  cadcells::Assignment& ass,
                                                  const covering_ng::VariableQuantification& variable_quantification,
                                                  const std::vector<carl::Variable>& var_order,
                                                  const std::map<carl::Variable, carl::Variable>& var_mapping) {

    auto [res, tree] = covering_ng::recurse_qe<typename Settings::op,
                                                typename Settings::formula_evaluation::Type,
                                                typename Settings::covering_heuristic,
                                                Settings::sampling_algorithm,
                                                typename Settings::cell_heuristic>
                                                (proj, f, ass, variable_quantification);
    
    if (!res.is_parameter()) return process_result(res);

    std::optional<RAN> optimum;
    bool optimum_strict = true;
    SMTRAT_STATISTICS_CALL(covering_ng::statistics().minimization_intervals(tree.children.size()));

    for (const auto& t : tree.children) {
        if (t.status != 1) continue;
        if (t.interval->lower().is_infty()) {
            mModel.assign(mObjectiveVariable, carl::InfinityValue{});
            break;
        }

        assert(t.interval->lower().value().is_root());
        RAN lb = carl::convert<RAN>(proj.evaluate({}, t.interval->lower().value().root()));
        if (!optimum || lb < optimum.value()) {
            optimum = lb;
            optimum_strict = t.interval->lower().is_strict();
            if (t.interval->upper().is_infty()) {
                m_minimization_max_epsilon = Rational(1);
            } else {
                RAN ub = carl::convert<RAN>(proj.evaluate({}, t.interval->upper().value().root()));
                Rational ub_rat = (ub.is_numeric() ? ub.value() : ub.interval().lower());
                Rational lb_rat = (optimum->is_numeric() ? optimum->value() : optimum->interval().upper());

                m_minimization_max_epsilon = ub_rat - lb_rat;
            }
        } else if (lb == optimum.value() && optimum_strict && t.interval->lower().is_weak()) {
            optimum_strict = false;
        }
    }

    if (optimum.has_value()) {
        if (optimum_strict) {
            carl::Variable eps = carl::fresh_real_variable("max_epsilon"); // TODO: hacky
            mModel.emplace(eps, m_minimization_max_epsilon);
            mModel.emplace(mObjectiveVariable, carl::Infinitesimal{optimum.value(), true});
        } else {
            mModel.emplace(mObjectiveVariable, optimum.value());
        }
    }
    // TODO: What about other variables?
    validation_minimize(Answer::OPTIMAL);
    return Answer::OPTIMAL;                    
}


template<typename Settings>
Answer CoveringNGModule<Settings>::process_result(const covering_ng::CoveringResult<typename Settings::op::PropertiesSet>& result) {
    if (result.is_unsat()) {
        mModel.clear();
        generateTrivialInfeasibleSubset();
        return Answer::UNSAT;
    }
    
    assert(result.is_failed());
    assert(!Settings::transform_boolean_variables_to_reals || result.is_failed_projection());
    mModel.clear();
    return Answer::UNKNOWN;
}


template<typename Settings>
void CoveringNGModule<Settings>::validation_minimize(const Answer a) {
    // input: min t s.t. f(x) ^ g(x) = t
    // found value: opt

    // unsat      |  input unsat
    // unbounded  |  for all t, x.(input(x,t) -> t >= t') unsat
    // closed     |  input(x,t) ^ [t < opt]  unsat and input(x,t) ^ [t = opt] sat
    // open       |  input(x,t) ^ [t <= opt] unsat and (not input(x,t)) ^ [opt < t] ^ [t < opt + max_delta] unsat


    FormulaT input(rReceivedFormula());
    if (a == Answer::UNSAT) {
        SMTRAT_VALIDATION_ADD("smtrat.covering", "minimization", input, false);
        return;
    }

    const auto& opt = mModel.at(mObjectiveVariable);

    if (opt.isMinusInfinity()) {
        auto free_vars = carl::free_variables(input);
        carl::Variable t_dash = carl::fresh_real_variable();
        std::vector<carl::Variable> vars(free_vars.begin(), free_vars.end());
        FormulaT v(
            carl::FormulaType::FORALL, vars,
            FormulaT(carl::FormulaType::IMPLIES,
                input,
                FormulaT(Poly(mObjectiveVariable) - Poly(t_dash), carl::Relation::GEQ)
            )
        );
        SMTRAT_VALIDATION_ADD("smtrat.covering", "minimization", v, false);
        return;
    }

    assert(opt.isRAN() || opt.isInfinitesimal());

    const RAN& ran = (opt.isRAN() ? opt.asRAN() : opt.asInfinitesimal().value);

    carl::Variable r = carl::fresh_real_variable();
    FormulaT ran_encode = (ran.is_numeric()
        ? FormulaT(carl::FormulaType::TRUE)
        : FormulaT(carl::FormulaType::AND, {
            FormulaT(Poly(carl::replace_main_variable(ran.polynomial(), r)), carl::Relation::EQ),
            FormulaT(Poly(r) - Poly(ran.interval().lower()), carl::Relation::GREATER),
            FormulaT(Poly(r) - Poly(ran.interval().upper()), carl::Relation::LESS)
        })
    );

    Poly p = Poly(mObjectiveVariable) - (ran.is_numeric() ? Poly(ran.value()) : Poly(r));

    FormulaT v(carl::FormulaType::AND, {
        input,
        ran_encode,
        FormulaT(p, (opt.isRAN() ? carl::Relation::LESS : carl::Relation::LEQ))
    });
    SMTRAT_VALIDATION_ADD("smtrat.covering", "minimization", v, false);

    if (opt.isRAN()) {
        FormulaT v2(carl::FormulaType::AND, {
            input,
            ran_encode,
            FormulaT(p, carl::Relation::EQ)
        });
        SMTRAT_VALIDATION_ADD("smtrat.covering", "optimum", v, true);
    } else {
        FormulaT v2(carl::FormulaType::AND, {
            input.negated(),
            ran_encode,
            FormulaT(p, carl::Relation::GREATER),
            FormulaT(p - Poly(m_minimization_max_epsilon), carl::Relation::LESS)
        });
        SMTRAT_VALIDATION_ADD("smtrat.covering", "optimum", v, false);
    }
}

} // namespace smtrat

