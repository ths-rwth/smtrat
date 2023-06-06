/**
 * @file SimplexModule.tpp
 * @author Valentin Promies
 *
 * @version 2023-04-28
 * Created on 2023-04-28.
 *
 * ================================================================================================
 * // N //  This file can be mostly read from top to bottom in the sense that
 * // O //  if a function f uses another function g, then g is implemented immediately **after** f.
 * // T //  So it can be read as "f : do sth including g, where g : ...".
 * // E //  This does not apply to auxiliary functions implemented in .h
 * ================================================================================================
 */

#include "SimplexModule.h"


/* ============================================================================================= */
/* /////////////////////////////////    Auxiliary Functions    ///////////////////////////////// */
/* ============================================================================================= */

namespace smtrat::simplex::helpers {

inline std::pair<BoundType, Rational> convert_relation(carl::Relation rel) {
    switch (rel) {
    case carl::Relation::GREATER: return { BoundType::LOWER, Rational(1) };
    case carl::Relation::GEQ:     return { BoundType::LOWER, Rational(0) };
    case carl::Relation::LESS:    return { BoundType::UPPER, Rational(-1)};
    case carl::Relation::LEQ:     return { BoundType::UPPER, Rational(0) };
    case carl::Relation::EQ:      return { BoundType::EQUAL, Rational(0) };
    case carl::Relation::NEQ:     return { BoundType::NEQ,   Rational(0) };
    default: assert(false);
    }
    return {BoundType::EQUAL, Rational(0)};
}

std::optional<Rational> find_scale(const Poly& l1, const Poly& l2) {
    // NOTE: This only works because polys are ordered!
    auto it1 = l1.begin();
    auto it2 = l2.begin();

    if (it1->single_variable() != it2->single_variable()) {
        return std::nullopt;
    }

    Rational scale = it2->coeff()/it1->coeff();
    ++it1;
    ++it2;
    while ((it1 != l1.end()) && (it2 != l2.end())) {
        if (it1->single_variable() != it2->single_variable()) {
            return std::nullopt;
        }
        if (scale * (it1->coeff()) != it2->coeff()) {
            return std::nullopt;
        }
        ++it1;
        ++it2;
        if ((it1 == l1.end()) != (it2 == l2.end())) return std::nullopt;
    }
    return scale;
}

}

namespace smtrat {

template<class Settings>
SimplexModule<Settings>::SimplexModule(const ModuleInput* _formula,
                                       Conditionals&      _conditionals,
                                       Manager*           _manager)
: Module( _formula, _conditionals, _manager ), m_bounds(), m_ref_cmp(m_bounds) {}

template<class Settings>
SimplexModule<Settings>::~SimplexModule() {}

template<class Settings>
void SimplexModule<Settings>::init() {}


/* ============================================================================================= */
/* ///////////////////////////////////////    Inform    //////////////////////////////////////// */
/* ============================================================================================= */

template<class Settings>
bool SimplexModule<Settings>::informCore( const FormulaT& f ) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "informed about" << f);

    if (f.type() != carl::FormulaType::CONSTRAINT) return true;
    if (f.constraint().is_consistent() == 0) return false;

    translate_variables(f);

    carl::Relation rel = f.constraint().relation();
    Poly lin_term = f.constraint().lhs();

    if constexpr (Settings::neq_handling == simplex::NEQHandling::NONE) {
        if (rel == carl::Relation::NEQ) return true;
    }

    SimplexVariable v;
    Rational coeff;
    Rational rhs = (-1)*lin_term.constant_part();
    lin_term += rhs;

    if (lin_term.is_univariate()) {
        v = m_to_simplex_var[lin_term.single_variable()];
        coeff = lin_term.lcoeff();
    } else {
        auto [_v, _coeff] = add_to_tableau(lin_term);
        v = _v;
        coeff = _coeff;
    }

    assert(!carl::is_zero(coeff));

    if (coeff < 0) rel = carl::turn_around(rel);
    rhs /= coeff;

    auto [type, delta] = simplex::helpers::convert_relation(rel);
    BoundRef b = m_bounds.add(v, type, DeltaRational(rhs, delta), f);
    add_bound_to_sets(b);
    return true;
}



template<class Settings>
void SimplexModule<Settings>::add_bound_to_sets(const BoundRef b) {
    switch (get_type(b)) {
    case BoundType::LOWER: { m_lower_bounds[get_variable(b)].emplace(b); break; }
    case BoundType::UPPER: { m_upper_bounds[get_variable(b)].emplace(b); break; }
    case BoundType::EQUAL: {
        m_lower_bounds[get_variable(b)].emplace(b);
        m_upper_bounds[get_variable(b)].emplace(b);
        break;
    }
    case BoundType::NEQ: {
        if constexpr (Settings::internal_neq_handling()) {
            m_neq_bounds[get_variable(b)].emplace(b);
        }
        break;
    }
    default: assert(false);
    }
}


template<class Settings>
std::pair<typename SimplexModule<Settings>::SimplexVariable, Rational> SimplexModule<Settings>::add_to_tableau(const Poly& linear_term) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "adding term " << linear_term << " to tableau");

    assert(!linear_term.has_constant_term());
    // is there already a slack variable for this linear term (maybe scaled by some coeff)?
    for (const auto& [lhs, var] : m_lhs_to_var) {
        auto scale = simplex::helpers::find_scale(lhs, linear_term);
        if (scale) return {var, *scale};
    }
    // none of the prior slacks fits => create a new one and add the respective row to the tableau
    SimplexVariable slack_var = new_slack_variable(linear_term);
    set_basic(slack_var, true);

    Tableau::RowID r = m_tableau.mk_row();
    assert(r == m_base.size());
    m_base.push_back(slack_var);
    m_base_coeffs.emplace_back(1);
    m_var_info[slack_var].m_tableau_index = r;
    for (const auto& term : linear_term) {
        m_tableau.add_var(r, term.coeff(), m_to_simplex_var.at(term.single_variable()));
    }
    m_tableau.add_var(r, Rational(-1), slack_var);

    return {slack_var, Rational(1)};
}


/* ============================================================================================= */
/* ///////////////////////////////////    Add / Activate    //////////////////////////////////// */
/* ============================================================================================= */

template<class Settings>
bool SimplexModule<Settings>::addCore( ModuleInput::const_iterator _subformula ) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "adding " << _subformula->formula());

    const FormulaT& f = _subformula->formula();
    if (f.type() == carl::FormulaType::FALSE) {
        FormulaSetT inf_subset;
        inf_subset.insert(f);
        mInfeasibleSubsets.push_back(inf_subset);
        return false;
    }
    if (f.type() != carl::FormulaType::CONSTRAINT) return true;

    if (f.constraint().relation() == carl::Relation::NEQ) {
        return activate_neq(f);
    }

    BoundRef b = m_bounds.get_from_origin(f);
    activate(b);
    SimplexVariable v = get_variable(b);
    return update_range(v,b);
}


template<class Settings>
bool SimplexModule<Settings>::update_range(const SimplexVariable v, const BoundRef b) {
    BoundType type = get_type(b);

    if (type == BoundType::UPPER || type == BoundType::EQUAL) {
        if (!has_upper_bound(v) || is_below(b, upper_bound(v))) {
            set_upper_bound(v,b);
            if (find_conflicting_lower_bounds(v,b)) return false;
        }
    }
    if (type == BoundType::LOWER || type == BoundType::EQUAL) {
        if (!has_lower_bound(v) || is_below(lower_bound(v), b)) {
            set_lower_bound(v,b);
            if (find_conflicting_upper_bounds(v,b)) return false;
        }
    }

    return true;
}

template<class Settings>
bool SimplexModule<Settings>::activate_neq(const FormulaT& f) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "activating neq " << f);

    if constexpr (Settings::neq_handling == simplex::NEQHandling::NONE) return true;
    if constexpr (Settings::neq_handling == simplex::NEQHandling::SPLITTING_ON_DEMAND) {
        m_neq_constraints.push_back(f);
    } else {
        activate(m_bounds.get_from_origin(f));
    }
    // TODO: quick check for conflicts with equalities?
    return true;
}

template<class Settings>
bool SimplexModule<Settings>::find_conflicting_lower_bounds(const SimplexVariable v, BoundRef b) {
    if (has_consistent_range(v)) return false;

    const DeltaRational& b_val = get_value(b);

    const BoundRef lb = lower_bound(v);
    if (is_derived(lb) && (get_value(lb) > b_val)) construct_infeasible_subset({lb, b});
    
    for (auto lb_it = m_lower_bounds[v].begin(); lb_it != m_lower_bounds[v].end(); ++lb_it) {
        if (is_active(*lb_it) && (get_value(*lb_it) > b_val))
            construct_infeasible_subset({*lb_it, b});
        if (*lb_it == lower_bound(v)) break; // NOTE: only works because bounds are ordered
    }
    return true;
}

template<class Settings>
bool SimplexModule<Settings>::find_conflicting_upper_bounds(const SimplexVariable v, BoundRef b) {
    if (has_consistent_range(v)) return false;

    const DeltaRational& b_val = get_value(b);

    const BoundRef ub = upper_bound(v);
    if (is_derived(ub) && (get_value(ub) < b_val)) construct_infeasible_subset({ub, b});

    for (auto ub_it = m_upper_bounds[v].rbegin(); ub_it != m_upper_bounds[v].rend(); ++ub_it) {
        if (is_active(*ub_it) && (get_value(*ub_it) < b_val))
            construct_infeasible_subset({*ub_it, b});
        if (*ub_it == upper_bound(v)) break; // NOTE: only works because bounds are ordered
    }
    return true;
}


template<class Settings>
void SimplexModule<Settings>::construct_infeasible_subset(const BoundVec& reason) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "constructing inf subset");
    FormulaSetT unsat_core;
    for (const auto& b : reason) {
        FormulaT origin = get_origin(b);
        if (origin.type() == carl::FormulaType::CONSTRAINT) {
            unsat_core.insert(origin);
        } else { // NOTE: assumes that the AND is flattened.
            assert(origin.type() == carl::FormulaType::AND);
            for (const auto& o : origin.subformulas()) {
                unsat_core.insert(o);
            }
        }
    }
    mInfeasibleSubsets.push_back(unsat_core);
}


/* ============================================================================================= */
/* ////////////////////////////////    Remove / Deactivate    ////////////////////////////////// */
/* ============================================================================================= */

template<class Settings>
void SimplexModule<Settings>::removeCore( ModuleInput::const_iterator _subformula ) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "removing" << _subformula->formula());

    const FormulaT& f = _subformula->formula();
    if (f.type() != carl::FormulaType::CONSTRAINT) return;
    assert(f.constraint().lhs().is_linear());

    if (f.constraint().relation() == carl::Relation::NEQ) {
        deactivate_neq(f);
        return;
    }

    BoundRef b = m_bounds.get_from_origin(f);
    deactivate(b);
    if constexpr (Settings::derive_bounds) {
        deactivate_bounds_derived_from(f);
    }

    SimplexVariable v = get_variable(b);
    update_range(v); // TODO: can we somehow move directly to the right bounds?
}


template<class Settings>
void SimplexModule<Settings>::deactivate_neq(const FormulaT& f) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "deactivating neq " << f);
    if constexpr (Settings::neq_handling == simplex::NEQHandling::NONE) return;
    if constexpr (Settings::neq_handling == simplex::NEQHandling::SPLITTING_ON_DEMAND) {
        auto it = std::find(m_neq_constraints.begin(), m_neq_constraints.end(), f);
        if (it != m_neq_constraints.end()) m_neq_constraints.erase(it);
    } else {
        deactivate(m_bounds.get_from_origin(f));
    }
}


template<class Settings>
void SimplexModule<Settings>::update_range(const SimplexVariable v) {
    // NOTE: the bound vectors are ordered ascendingly by bound value
    // Therefore we use the reverse iterator for lower bounds

    auto it_lower = m_lower_bounds[v].rbegin();
    for (; it_lower != m_lower_bounds[v].rend(); ++it_lower) {
        if (is_active(*it_lower)) {
            set_lower_bound(v, *it_lower);
            break;
        }
    }
    if (it_lower == m_lower_bounds[v].rend()) set_lower_unbounded(v);

    auto it_upper = m_upper_bounds[v].begin();
    for (; it_upper != m_upper_bounds[v].end(); ++it_upper) {
        if (is_active(*it_upper)) {
            set_upper_bound(v, *it_upper);
            break;
        }
    }
    if (it_upper == m_upper_bounds[v].end()) set_upper_unbounded(v);
}


template<class Settings>
void SimplexModule<Settings>::deactivate_bounds_derived_from(const FormulaT& f) {
    assert(Settings::derive_bounds);
    SMTRAT_LOG_DEBUG("smtrat.simplex", "deactivating derived bounds");
    auto it = m_bounds_derived_from.find(f);
    if (it == m_bounds_derived_from.end()) return;

    for (const auto& b : it->second) {
        if (!is_active(b)) continue;

        deactivate(b);
        SimplexVariable v = get_variable(b);
        update_range(v); // TODO: can we somehow move directly to the right bounds?
    }
}


/* ============================================================================================= */
/* ///////////////////////////////////    Rational Model    //////////////////////////////////// */
/* ============================================================================================= */

template<class Settings>
void SimplexModule<Settings>::updateModel() const {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "updating model, computed before? " << m_model_computed);
    if (m_model_computed) return;
    // TODO: find an efficient way to avoid unnecessary computations
    // (e.g. only update delta if needed)

    // compute suitable delta
    Rational delta = 1;
    for (SimplexVariable v = 0; v < m_num_variables; ++v) {
        if (carl::is_zero(m_assignment[v].delta())) continue;

        if (has_lower_bound(v)) {
            const DeltaRational& bound_val = get_value(lower_bound(v));
            const DeltaRational& assigned_val = m_assignment[v];
            Rational delta_diff = bound_val.delta() - assigned_val.delta();

            if (delta_diff > 0) {
                Rational delta_bound = (assigned_val.real() - bound_val.real()) / delta_diff;
                if (delta_bound < delta) delta = delta_bound;
            }
        }

        if (has_upper_bound(v)) {
            const DeltaRational& bound_val = get_value(upper_bound(v));
            const DeltaRational& assigned_val = m_assignment[v];
            Rational delta_diff = assigned_val.delta() - bound_val.delta();

            if (delta_diff > 0) {
                Rational delta_bound = (bound_val.real() - assigned_val.real()) / delta_diff;
                if (delta_bound < delta) delta = delta_bound;
            }
        }
    }


    assert(delta > 0);
    // TODO: NEQ handling?
    // TODO: find nice value for delta
    // transform m_assignment into rational model

    for (const auto [carl_var, simplex_var] : m_to_simplex_var) {
        const auto& asgn = m_assignment[simplex_var];
        Rational val = asgn.real() + (delta * asgn.delta());
        mModel.assign(carl_var, val);
    }

    m_model_computed = true;
}

/* ============================================================================================= */
/* //////////////////////////////////    Check / Simplex    //////////////////////////////////// */
/* ============================================================================================= */

template<class Settings>
Answer SimplexModule<Settings>::checkCore() {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "checking...");
    /*
     * Not yet clear: SOI, optimization, integer...
     */

    if constexpr (Settings::reactivate_derived_bounds) {
        if (!reactivate_derived_bounds()) {
            SMTRAT_LOG_DEBUG("smtrat.simplex", "reactivating bounds lead to conflict");
            return Answer::UNSAT;
        }
    }

    if constexpr (Settings::simple_theory_propagation) {
        simple_theory_propagation();
    }

    m_num_pivots = 0;

    build_initial_assignment();
    while (exist_violated_bounds()) {
        auto conflict_or_pivot = find_conflict_or_pivot();

        if (conflict_or_pivot.is_conflict()) {
            construct_infeasible_subset(conflict_or_pivot.conflict());
            return Answer::UNSAT;
        }

        pivot_and_update(conflict_or_pivot.pivot_candidate());

        // Bound learning after pivot can lead to conflicts, stored in mInfeasibleSubsets
        if (!mInfeasibleSubsets.empty()) {
            SMTRAT_LOG_DEBUG("smtrat.simplex", "Deriving bounds lead to conflict");
            return Answer::UNSAT;
        }
    }

    m_model_computed = false;
    updateModel();

    if constexpr (Settings::neq_handling == simplex::NEQHandling::SPLITTING_ON_DEMAND) {
        if (!check_neqs()) return Answer::UNKNOWN;
    }

    return Answer::SAT;
}


template<class Settings>
bool SimplexModule<Settings>::reactivate_derived_bounds() {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "reactivating derived bounds");
    assert(Settings::reactivate_derived_bounds);
    for (const BoundRef b : m_derived_bounds) {
        if (is_active(b)) continue;
        const FormulaT& origins_of_b = get_origin(b);
        assert(origins_of_b.type() == carl::FormulaType::AND);
        bool all_origins_active = true;
        for (const auto& o : origins_of_b.subformulas()) {
            if (!is_active(m_bounds.get_from_origin(o))) {
                all_origins_active = false;
                break;
            }
        }
        if (all_origins_active) {
            SMTRAT_LOG_DEBUG("smtrat.simplex", "reactivating " << m_bounds[b]);
            activate(b);
            SimplexVariable v = get_variable(b);
            if (!update_range(v, b)) return false;
        }
    }
    return true;
}


template<class Settings>
void SimplexModule<Settings>::build_initial_assignment() {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "building initial assignment");

    if (m_assignment.empty()) {
        m_assignment.resize(m_num_variables);
        for (SimplexVariable v = 0; v < m_num_variables; ++v) {
            if (is_basic(v)) continue;
            else if (has_lower_bound(v)) m_assignment[v] = get_value(lower_bound(v));
            else if (has_upper_bound(v)) m_assignment[v] = get_value(upper_bound(v));
            else m_assignment[v] = DeltaRational(0);
        }
    } else {
        // there is an assignment from a previous run
        for (SimplexVariable v = 0; v < m_num_variables; ++v) {
            if (is_basic(v)) continue;
            if (assigned_in_range(v)) continue;
            if (has_lower_bound(v))    m_assignment[v] = get_value(lower_bound(v));
            else /*(has_upper_bound(v)) */ m_assignment[v] = get_value(upper_bound(v));
        }
    }
    compute_basic_assignment();
}


template<class Settings>
void SimplexModule<Settings>::compute_basic_assignment() {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "computing basic assignment");
    for (Tableau::RowID r = 0; r < m_tableau.num_rows(); ++r) {
        SimplexVariable basic_var = m_base[r];
        DeltaRational& val = m_assignment[basic_var];
        val = Rational(0);
        for (const auto& entry : m_tableau.get_row(r)) {
            if (entry.var() == basic_var) continue;
            val += (m_assignment[entry.var()] * entry.coeff());
        }
        val /= m_base_coeffs[r];
    }

    m_changed_basic_vars.clear();
    m_changed_basic_vars.insert(m_base.begin(), m_base.end());
}


template<class Settings>
bool SimplexModule<Settings>::exist_violated_bounds() {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "looking for violated bounds");

    m_violated_bounds.clear();
    std::vector<SimplexVariable> no_fix_needed;
    for (SimplexVariable v : m_changed_basic_vars) {
        bool needs_fix = false;
        if (has_lower_bound(v)) {
            BoundRef b = lower_bound(v);
            if (m_assignment[v] < get_value(b)) {
                m_violated_bounds.push_back(b);
                needs_fix = true;
            }
        }
        if (has_upper_bound(v)) {
            BoundRef b = upper_bound(v);
            if (m_assignment[v] > get_value(b)) {
                m_violated_bounds.push_back(b);
                needs_fix = true;
            }
        }
        if (!needs_fix) no_fix_needed.push_back(v);
    }
    for (SimplexVariable v : no_fix_needed) m_changed_basic_vars.erase(v);

    // TODO: NEQHandling
    return !m_violated_bounds.empty();
}


template<class Settings>
SimplexModule<Settings>::ConflictOrPivot SimplexModule<Settings>::find_conflict_or_pivot() {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "looking for conflict or pivot");

    PivotCandidates possible_pivots;

    for (const auto& b : m_violated_bounds) {
        SimplexVariable basic_var = get_variable(b);
        assert(is_basic(basic_var));
        bool lower_violated = (get_type(b) == BoundType::LOWER) || (violates_lower(basic_var));
        bool increase = ((m_base_coeffs[get_tableau_index(basic_var)] > 0) == lower_violated);
        auto [it, _] = possible_pivots.emplace(basic_var, std::vector<const Tableau::Entry*>());
        auto& suitable_entries = it->second;
        Tableau::RowID r = get_tableau_index(basic_var);

        BoundVec conflict;
        conflict.reserve(m_tableau.row_size(r));
        conflict.push_back(b);

        for (const auto& entry : m_tableau.get_row(r)) {
            SimplexVariable non_basic_var = entry.var();
            if (non_basic_var == basic_var) continue;
            assert(!is_basic(non_basic_var));
            auto prohibitive_bound = check_suitable_for_pivot(entry, b, increase);
            if (prohibitive_bound) {
                conflict.push_back(*prohibitive_bound);
            } else {
                suitable_entries.push_back(&entry);
            }
        }
        if (suitable_entries.empty()) return ConflictOrPivot::mk_conflict(conflict);
    }

    // Choose pivot element according to some strategy
    return ConflictOrPivot::mk_pivot(choose_pivot(possible_pivots));
}


template<class Settings>
std::optional<typename SimplexModule<Settings>::BoundRef> SimplexModule<Settings>::check_suitable_for_pivot(const Tableau::Entry& entry,
                                                                                                            const BoundRef b,
                                                                                                            bool increase) const {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "checking suitability for pivot");
    // TODO: use b to have further restrictions

    if (increase == (entry.coeff() > 0)) {
        if (is_at_upper(entry.var())) return upper_bound(entry.var());
        return std::nullopt;
    }

    if (is_at_lower(entry.var())) return lower_bound(entry.var());
    return std::nullopt;
}


template<class Settings>
SimplexModule<Settings>::PivotCandidate SimplexModule<Settings>::choose_pivot(const PivotCandidates& possible_pivots) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "choosing pivot from candidates");

    assert(possible_pivots.size() != 0);

    // check whether Blands rule should be used to escape cycling
    if (should_use_blands()) return choose_pivot_bland(possible_pivots);

    // otherwise apply chosen heuristic strategy
    if constexpr (Settings::pivot_strategy == simplex::PivotStrategy::MIN_ROW_MIN_COL) {
        return choose_pivot_heur(possible_pivots);
    }
    if constexpr (Settings::pivot_strategy == simplex::PivotStrategy::FMPLEX) {
        return choose_pivot_fmplex(possible_pivots);
    }

    return choose_pivot_bland(possible_pivots);
}


template<class Settings>
SimplexModule<Settings>::PivotCandidate SimplexModule<Settings>::choose_pivot_heur(const PivotCandidates& possible_pivots) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "using heuristic");

    auto min_row_it = possible_pivots.begin();
    std::size_t min_row_len = m_tableau.num_vars();

    for (auto it = min_row_it; it != possible_pivots.end(); ++it) {
        std::size_t row_len = m_tableau.row_size(get_tableau_index(it->first));
        if (row_len < min_row_len) {
            min_row_it = it;
            min_row_len = row_len;
        }
        // TODO: tiebreaker
    }

    const auto& col_candidates = min_row_it->second;

    auto min_col_it = col_candidates.begin();
    std::size_t min_col_len = m_tableau.num_rows();

    for (auto it = min_col_it; it != col_candidates.end(); ++it) {
        std::size_t col_len = m_tableau.column_size(get_tableau_index((*it)->var()));
        if (col_len < min_col_len) {
            min_col_it = it;
            min_col_len = col_len;
        }
        // TODO: tiebreaker
    }

    return PivotCandidate(min_row_it->first, **min_col_it);
}


template<class Settings>
SimplexModule<Settings>::PivotCandidate SimplexModule<Settings>::choose_pivot_bland(const PivotCandidates& possible_pivots) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "using blands rule");

    auto [lowest_row_var, column_vars] = *possible_pivots.begin();
    assert(!column_vars.empty());
    const Tableau::Entry* lowest_col_var_entry = column_vars.front();

    for (auto entry_ptr : column_vars) {
        if (entry_ptr->var() < lowest_col_var_entry->var()) lowest_col_var_entry = entry_ptr;
    }
    return PivotCandidate(lowest_row_var, *lowest_col_var_entry);
}

template<class Settings>
void SimplexModule<Settings>::pivot_and_update(PivotCandidate pivot_candidate) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "pivot and update");

    SimplexVariable x_i = pivot_candidate.basic_var();
    SimplexVariable x_j = pivot_candidate.nonbasic_var();

    // TODO: make the value needed to fix more accessible (also for is_suitable)
    DeltaRational diff = violates_lower(x_i) ? get_value(lower_bound(x_i)) - m_assignment[x_i]
                                             : get_value(upper_bound(x_i)) - m_assignment[x_i];

    pivot(x_i, x_j, pivot_candidate.coeff());
    update(x_i, diff);

    if constexpr (Settings::derive_bounds) {
        derive_bounds(get_tableau_index(x_j));
    }

    m_changed_basic_vars.erase(x_i);
}


template<class Settings>
void SimplexModule<Settings>::update(SimplexVariable nonbase_var, const DeltaRational& diff) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "update");

    // Already updates the basic variables
    m_assignment[nonbase_var] += diff;
    auto end = m_tableau.col_end(nonbase_var);
    for (auto it = m_tableau.col_begin(nonbase_var); it != end; ++it) {
        Tableau::RowID r = it.get_row();
        SimplexVariable base_var      = m_base[r];
        const Rational& base_coeff    = m_base_coeffs[r];
        const Rational& nonbase_coeff = it.get_row_entry().coeff();
        m_assignment[base_var] += diff * (nonbase_coeff/base_coeff);
        m_changed_basic_vars.insert(base_var);
    }
}


template<class Settings>
void SimplexModule<Settings>::pivot(SimplexVariable x_i, SimplexVariable x_j, const Rational& a_ij) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "pivot");

    // swap basic and nonbasic
    Tableau::RowID r_i = get_tableau_index(x_i);
    m_base[r_i] = x_j;
    // todo nobase, update x_i
    set_tableau_index(x_j, r_i);
    set_tableau_index(x_i, x_i);
    set_basic(x_j, true );
    set_basic(x_i, false);

    m_base_coeffs[r_i] = -a_ij;
    m_changed_basic_vars.insert(x_j);

    Rational a_kj, g;
    auto end = m_tableau.col_end(x_j);
    for (auto it = m_tableau.col_begin(x_j); it != end; ++it) {
        Tableau::RowID r_k = it.get_row();
        if (r_k == r_i) continue;

        // TODO: this does not use that we know column j will be mostly zeros
        a_kj = (-1) * it.get_row_entry().coeff();
        m_tableau.mul(r_k, a_ij);
        m_tableau.add(r_k, a_kj, r_i);

        m_base_coeffs[r_k] *= a_ij;

        m_tableau.gcd_normalize(r_k, g);
        if (!carl::is_one(g)) m_base_coeffs[r_k] /= g;
    }
    ++m_num_pivots;
}


template<class Settings>
bool SimplexModule<Settings>::check_neqs() {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "checking neqs with model " << mModel);

    static_assert(Settings::neq_handling == simplex::NEQHandling::SPLITTING_ON_DEMAND);
    bool all_satisfied = true;
    for (const auto& neq : m_neq_constraints) {
        if (!carl::satisfied_by(neq, mModel)) {
            SMTRAT_LOG_DEBUG("smtrat.simplex", "NEQ " << neq << " is not satisfied!");
            all_satisfied = false;
            splitUnequalConstraint(neq);
        }
    }
    return all_satisfied;
}


/* ============================================================================================= */
/* ///////////////////////////////////    Bound Learning    //////////////////////////////////// */
/* ============================================================================================= */


template<class Settings>
void SimplexModule<Settings>::derive_bounds(const Tableau::RowID rid) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "derive bounds for row  " << rid);
    bool equal_derivable = true;
    bool lower_derivable = true;
    bool upper_derivable = true;

    for (const auto& entry : m_tableau.get_row(rid)) {
        SimplexVariable entry_var = entry.var();
        if (entry_var == m_base[rid]) continue; // REVIEW: can we make this more efficient?
        bool pos_coeff = (entry.coeff() > 0);

        if (!has_lower_bound(entry_var)) {
            if (pos_coeff) lower_derivable = false;
            else upper_derivable = false;
            equal_derivable = false;
        } else if (get_type(lower_bound(entry_var)) != BoundType::EQUAL) {
            equal_derivable = false;
        }

        if (!has_upper_bound(entry_var)) {
            if (pos_coeff) upper_derivable = false;
            else lower_derivable = false;
            equal_derivable = false;
        } else if (get_type(upper_bound(entry_var)) != BoundType::EQUAL) {
            equal_derivable = false;
        }
    }

    if (equal_derivable) derive_bound(rid, BoundType::EQUAL);
    else {
        if (lower_derivable) derive_bound(rid, BoundType::LOWER);
        if (upper_derivable) derive_bound(rid, BoundType::UPPER);
    }
}


template<class Settings>
void SimplexModule<Settings>::derive_bound(const Tableau::RowID rid, const BoundType type) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "derive single bound for row " << rid);
    DeltaRational new_bound_value(Rational(0));
    bool lower_or_equal = ((type == BoundType::LOWER) || (type == BoundType::EQUAL));
    SimplexVariable base_var = m_base[rid];

    std::vector<BoundRef> involved_bounds;

    for (const auto& entry : m_tableau.get_row(rid)) {
        SimplexVariable entry_var = entry.var();
        if (entry_var == base_var) continue; // REVIEW: can we make this more efficient?
        bool pos_coeff = (entry.coeff() > 0);
        // use lower bound if: (we derive a lower bound <=> the coeff is positive)
        BoundRef b = (lower_or_equal == pos_coeff) ? lower_bound(entry_var)
                                                   : upper_bound(entry_var);
        involved_bounds.push_back(b);
        new_bound_value += (get_value(b) * entry.coeff());
    }

    const Rational& base_coeff = m_base_coeffs[rid];
    new_bound_value /= base_coeff;

    if (type == BoundType::EQUAL) {
        if (!has_lower_bound(base_var) || (new_bound_value > get_value(lower_bound(base_var))) ||
            !has_upper_bound(base_var) || (new_bound_value < get_value(upper_bound(base_var)))) {
            add_derived_bound(base_var, BoundType::EQUAL, new_bound_value, involved_bounds);
        }
    } else if ((base_coeff > 0) == lower_or_equal) {
        // derived bound is a lower bound on var if (it's a lower bound <=> base coeff is >0)
        if (!has_lower_bound(base_var) || new_bound_value > get_value(lower_bound(base_var))) {
            add_derived_bound(base_var, BoundType::LOWER, new_bound_value, involved_bounds);
        }
    } else {
        if (!has_upper_bound(base_var) || new_bound_value < get_value(upper_bound(base_var))) {
            add_derived_bound(base_var, BoundType::UPPER, new_bound_value, involved_bounds);
        }
    }

    if (!has_consistent_range(base_var)) {
        SMTRAT_LOG_DEBUG("smtrat.simplex", "Derived Conflict: " << m_bounds[lower_bound(base_var)]
                                            << ", " << m_bounds[upper_bound(base_var)]);

        construct_infeasible_subset({lower_bound(base_var), upper_bound(base_var)});
    }
}


template<class Settings>
void SimplexModule<Settings>::add_derived_bound(const SimplexVariable var,
                                                const BoundType type,
                                                const DeltaRational& value,
                                                const BoundVec& premises) {
    // collect the origins of all premises
    FormulaSetT single_origins;
    for (const BoundRef p : premises) {
        const FormulaT& o = get_origin(p);
        if (o.type() == carl::FormulaType::AND) {
            for (const auto& c : o.subformulas()) single_origins.insert(c);
        } else {
            single_origins.insert(o);
        }
    }
    const FormulaT origin_conj = FormulaT(carl::FormulaType::AND, single_origins);

    // create the bound, add it to bookkeeping
    const BoundRef b = m_bounds.add_derived(var, type, value, origin_conj);
    m_derived_bounds.push_back(b);
    activate(b);
    for (const auto& o : single_origins) {
        m_bounds_derived_from[o].push_back(b);
    }
    SMTRAT_LOG_DEBUG("smtrat.simplex", "Add " << m_bounds[b] << " derived from " << origin_conj);

    // update range and learn lemmas
    switch (type) {
    case BoundType::EQUAL: {
        // this extra check is for catching conflicting bounds.
        // If we set both bounds at once, we might miss a conflict
        if (!has_lower_bound(var) || (value > get_value(lower_bound(var)))) {
            set_lower_bound(var, b);
            propagate_derived_lower(var, b);
        }
        if (!has_upper_bound(var) || (value < get_value(upper_bound(var)))) {
            set_upper_bound(var, b);
            propagate_derived_upper(var, b);
        }
        break;
    }
    case BoundType::LOWER: { 
        set_lower_bound(var, b);
        propagate_derived_lower(var, b);
        break;
    }
    case BoundType::UPPER: {
        set_upper_bound(var, b);
        propagate_derived_upper(var, b);
        break;
    }
    default: assert(false);
    }
}


template<class Settings>
void SimplexModule<Settings>::propagate_derived_lower(const SimplexVariable v, const BoundRef b) {
    if constexpr (!Settings::create_lemmas_from_derived) return;

    // iterate from strictest (greatest) lb to weakest (lowest) -> reverse_iterator
    for (auto it = m_lower_bounds[v].rbegin(); it != m_lower_bounds[v].rend() ++it) {
        if (!is_below(*it, b)) {
            // it is next weaker lower bound
            propagate(b, *it);
            break;
        }
    }
}

template<class Settings>
void SimplexModule<Settings>::propagate_derived_upper(const SimplexVariable v, const BoundRef b) {
    if constexpr (!Settings::create_lemmas_from_derived) return;

    // iterate from strictest (lowest) ub to weakest (greatest) -> forward iterator
    for (auto it = m_upper_bounds[v].begin(); it != m_upper_bounds[v].end() ++it) {
        if (!is_below(b, *it)) {
            // it is next weaker upper bound
            propagate(b, *it);
            break;
        }
    }
}


/* ============================================================================================= */
/* /////////////////////////////////    Theory Propagation    ////////////////////////////////// */
/* ============================================================================================= */


template<class Settings>
void SimplexModule<Settings>::simple_theory_propagation() {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "simple theory propagation");
    for (const auto& range : m_ranges) {
        if (range.has_lower()) {
            const BoundRef b = range.lower();
            assert(is_active(b));
            if (get_type(b) == BoundType::EQUAL) propagate_equal(b);
            else propagate_lower(b);
        }
        if (range.has_upper() && (get_type(range.upper()) != BoundType::EQUAL)) {
            const BoundRef b = range.upper();
            assert(is_active(b));
            propagate_upper(b);
        }
    }
}

template<class Settings>
void SimplexModule<Settings>::propagate_lower(const BoundRef b) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "propagating lower bound");
    const auto& ubs = m_upper_bounds[get_variable(b)];
    // iterating from lowest ub to highest ub
    for (auto upper_it = ubs.begin(); upper_it != ubs.end(); ++upper_it) {
        if (!is_below(*upper_it, b)) break;
        if (is_active(*upper_it)) continue; // TODO: what about is_active("complement(upper_bound)")?
        // TODO: also, can't we leave out is_active here? if it were active, then there woudl have
        // been a conflict while activating...
        // TODO: if it is an EQUAL bound, we might need to consider NEQ handling
        propagate_negated(b, *upper_it);
    }

    const auto& lbs = m_lower_bounds[get_variable(b)];
    // iterating from lowest lb to highest lb
    for (auto lower_it = lbs.begin(); lower_it != lbs.end(); ++lower_it) {
        if (b == *lower_it) break;
        if (is_below(b, *lower_it)) break;

        if (is_active(*lower_it)) continue;
        if (get_type(*lower_it) == BoundType::EQUAL) continue;

        propagate(b, *lower_it);
    }
}


template<class Settings>
void SimplexModule<Settings>::propagate_upper(const BoundRef b) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "propagating upper bound");
    const auto& lbs = m_lower_bounds[get_variable(b)];
    // iterating from highest lb to lowest lb => reverse iterator
    for (auto lower_it = lbs.rbegin(); lower_it != lbs.rend(); ++lower_it) {
        if (!is_below(b, *lower_it)) break;
        if (is_active(*lower_it)) continue; // TODO: what about is_active("complement(lower_bound)")?
        // TODO: if it is an EQUAL bound, we might need to consider NEQ handling
        propagate_negated(b, *lower_it);
    }

    const auto& ubs = m_upper_bounds[get_variable(b)];
    // iterating from highest ub to lowest ub => reverse iterator
    for (auto upper_it = ubs.rbegin(); upper_it != ubs.rend(); ++upper_it) {
        if (b == *upper_it) break;
        if (is_below(*upper_it, b)) break;

        if (is_active(*upper_it)) continue;
        if (get_type(*upper_it) == BoundType::EQUAL) continue;

        propagate(b, *upper_it);
    }
}


template<class Settings>
void SimplexModule<Settings>::propagate_equal(const BoundRef b) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "propagating equal bound");
    // TODO: we might need to consider NEQ handling
    const auto& lbs = m_lower_bounds[get_variable(b)];
    auto lower_it = lbs.begin();
    // iterating from lowest lb to highest lb
    for (; lower_it != lbs.end() && is_below(*lower_it, b); ++lower_it) {
        if (is_active(*lower_it)) continue;
        if (get_type(*lower_it) == BoundType::EQUAL) {
            propagate_negated(b, *lower_it);
        } else {
            propagate(b, *lower_it);
        }
    }

    for (; lower_it != lbs.end() && !is_below(b, *lower_it); ++lower_it) {
        if (!is_active(*lower_it)) propagate(b, *lower_it);
    }

    for (; lower_it != lbs.end(); ++lower_it) {
        if (is_active(*lower_it)) continue; // TODO: what about is_active("complement(lower_bound)")?
        propagate_negated(b, *lower_it);
    }

    const auto& ubs = m_upper_bounds[get_variable(b)];
    auto upper_it = ubs.begin();
    // iterating from lowest ub to highest ub
    for (; upper_it != ubs.end() && is_below(*upper_it, b); ++upper_it) {
        if (is_active(*upper_it)) continue; // TODO: what about is_active("complement(lower_bound)")?
        if (get_type(*upper_it) == BoundType::EQUAL) continue; 

        propagate_negated(b, *upper_it);
    }

    for (; upper_it != ubs.end(); ++upper_it) {
        if (is_active(*upper_it)) continue;
        if (get_type(*upper_it) == BoundType::EQUAL) continue; 
        propagate(b, *upper_it);
    }
}

template<class Settings>
void SimplexModule<Settings>::propagate(const BoundRef premise, const BoundRef conclusion) {
    FormulasT premise_origins;
    collectOrigins(get_origin(premise), premise_origins);
    FormulaT conclusion_formula = get_origin(conclusion);
    SMTRAT_LOG_DEBUG("smtrat.simplex", "("<< premise_origins <<") => ("<< conclusion_formula <<")");
    
    mTheoryPropagations.emplace_back(std::move(premise_origins), conclusion_formula);
}

template<class Settings>
void SimplexModule<Settings>::propagate_negated(const BoundRef premise, const BoundRef conclusion) {
    FormulasT premise_origins;
    collectOrigins(get_origin(premise), premise_origins);
    FormulaT conclusion_formula = get_origin(conclusion).negated();
    SMTRAT_LOG_DEBUG("smtrat.simplex", "("<< premise_origins <<") => ("<< conclusion_formula <<")");
    
    mTheoryPropagations.emplace_back(std::move(premise_origins), conclusion_formula);
}

}
