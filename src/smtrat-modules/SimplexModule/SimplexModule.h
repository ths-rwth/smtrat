/**
 * @file SimplexModule.h
 * @author Valentin Promies
 *
 * @version 2023-04-28
 * Created on 2023-04-28.
 */

#pragma once

#include <smtrat-solver/Module.h>
#include "SimplexSettings.h"
#include "simplex/DeltaValue.h"
#include "simplex/VariableInfo.h"
#include "simplex/Bound.h"
#include "simplex/Tableau.h"

namespace smtrat {

template<typename Settings>
class SimplexModule : public Module {

/* ============================================================================================= */
/* //////////////////////////////////    Type Definitions    /////////////////////////////////// */
/* ============================================================================================= */
private:
    using SimplexVariable = std::size_t; // TODO: make it so it becomes clear that this is
                                         // the same type as Tableau::ColID and Bound::Var
    using DeltaRational   = simplex::DeltaValue<Rational>;
    using Tableau         = simplex::Tableau<Rational>;

    using Bound           = simplex::Bound<DeltaRational>;
    using BoundType       = simplex::BoundType;
    using Bounds          = simplex::Bounds<DeltaRational>;
    using BoundRef        = Bounds::Ref;
    using BoundSet        = BoundRef::Set;
    using BoundVec        = std::vector<BoundRef>;

    using VarIndex        = std::map<carl::Variable, SimplexVariable>;

    struct Range {
        std::optional<BoundRef> m_lower = std::nullopt;
        std::optional<BoundRef> m_upper = std::nullopt;
        Range() {}
        bool has_lower() const { return m_lower.has_value(); }
        bool has_upper() const { return m_upper.has_value(); }
        BoundRef lower() const { assert(m_lower); return *m_lower; }
        BoundRef upper() const { assert(m_upper); return *m_upper; }
    };

    struct PivotCandidate {
        SimplexVariable       m_basic_var;
        const Tableau::Entry& mr_nonbasic;

        Tableau::RowID basic_var   () const { return m_basic_var; }
        Tableau::ColID nonbasic_var() const { return mr_nonbasic.var(); }
        Rational       coeff       () const { return mr_nonbasic.coeff(); }

        PivotCandidate(SimplexVariable v, const Tableau::Entry& e)
        : m_basic_var(v), mr_nonbasic(e) {}
    };

    using PivotCandidates = std::map<SimplexVariable, std::vector<const Tableau::Entry*>>;

    class ConflictOrPivot {
    private:
        std::variant<BoundVec, PivotCandidate> m_value;
        explicit ConflictOrPivot(const BoundVec& cf) : m_value(cf) {}
        explicit ConflictOrPivot(const PivotCandidate& pc) : m_value(pc) {}
    public:
        bool is_conflict() const { return std::holds_alternative<BoundVec>(m_value); }

        BoundVec conflict() const {
            assert(is_conflict());
            return std::get<BoundVec>(m_value);
        }

        PivotCandidate pivot_candidate() const {
            assert(!is_conflict());
            return std::get<PivotCandidate>(m_value);
        }

        static ConflictOrPivot mk_conflict(BoundVec cf)    { return ConflictOrPivot(cf); }
        static ConflictOrPivot mk_pivot(PivotCandidate pc) { return ConflictOrPivot(pc); }
    };

/* ============================================================================================= */
/* //////////////////////////////////        Members        //////////////////////////////////// */
/* ============================================================================================= */

    // information about variables
    std::size_t                        m_num_variables = 0;
    VarIndex                           m_to_simplex_var;
    std::vector<simplex::VariableInfo> m_var_info;

    // stored assignments
    std::vector<DeltaRational>         m_assignment;
    mutable bool                       m_model_computed = false;
    std::set<SimplexVariable>          m_changed_basic_vars;

    // the tableau
    Tableau                            m_tableau;
    std::vector<SimplexVariable>       m_base;        // = map : Tableau::RowID -> SimplexVariable
    std::vector<Rational>              m_base_coeffs; // = map : Tableau::RowID -> Rational
    std::vector<SimplexVariable>       m_nonbase;     // = map : Tableau::ColID -> SimplexVariable
    // TODO: use nonbase? we can store a variable's index in the nonbase in tableau_index (rename)
    // build_initial_assignment could be made more efficient with that.

    std::size_t                        m_num_pivots = 0;

    // stored bounds
    Bounds                             m_bounds;          // owns the bounds
    std::vector<BoundSet>              m_lower_bounds;
    std::vector<BoundSet>              m_upper_bounds;
    std::vector<Range>                 m_ranges;
    BoundVec                           m_violated_bounds; // temporary storage
    BoundRef::cmp                      m_ref_cmp;

    BoundVec                           m_derived_bounds;
    std::map<FormulaT, BoundVec>       m_bounds_derived_from;

    std::map<Poly, SimplexVariable>    m_lhs_to_var;

    // NEQHandling
    FormulasT                          m_neq_constraints; // used by SPLITTING_ON_DEMAND
    std::vector<BoundSet>              m_neq_bounds;      // used by UPDATE_PERTURBATION and PIVOT


/* ============================================================================================= */
/* //////////////////////////////////    Public Interfaces    ////////////////////////////////// */
/* ============================================================================================= */
public:

    SimplexModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

    ~SimplexModule();


    typedef Settings SettingsType;
    std::string moduleName() const {
        return SettingsType::moduleName;
    }

    /**
     * Informs the module about the given constraint. It should be tried to inform this
     * module about any constraint it could receive eventually before assertSubformula
     * is called (preferably for the first time, but at least before adding a formula
     * containing that constraint).
     * @param _constraint The constraint to inform about.
     * @return false, if it can be easily decided whether the given constraint is inconsistent;
     *          true, otherwise.
     */
    bool informCore( const FormulaT& _constraint );

    /**
     * Informs all backends about the so far encountered constraints
     * which have not yet been communicated.
     * This method must not and will not be called more than once
     * and only before the first runBackends call.
     */
    void init();

    /**
     * The module has to take the given sub-formula of the received formula into account.
     *
     * @param _subformula The sub-formula to take additionally into account.
     * @return false, if it can be easily decided that this sub-formula causes a conflict with
     *           the already considered sub-formulas;
     *           true, otherwise.
     */
    bool addCore( ModuleInput::const_iterator _subformula );

    /**
     * Removes the subformula of the received formula at the given position
     * to the considered ones of this module.
     * Note that this includes every stored calculation which depended on this subformula,
     * but should keep the other stored calculation, if possible, untouched.
     *
     * @param _subformula The position of the subformula to remove.
     */
    void removeCore( ModuleInput::const_iterator _subformula );

    /**
     * Updates the current assignment into the model.
     * Note that this is a unique but possibly symbolic assignment
     * maybe containing newly introduced variables.
     */
    void updateModel() const;

    /**
     * Checks the received formula for consistency.
     * @return True,    if the received formula is satisfiable;
     *         False,   if the received formula is not satisfiable;
     *         Unknown, otherwise.
     */
    Answer checkCore();

/* ============================================================================================= */
/* //////////////////////////////////    Interior Methods    /////////////////////////////////// */
/* ============================================================================================= */
private:

/* ============================= Access to Bound data via BoundRef ============================= */

    const DeltaRational& get_value   (BoundRef bound_ref) const { return m_bounds[bound_ref].m_value;      }
    SimplexVariable      get_variable(BoundRef bound_ref) const { return m_bounds[bound_ref].m_var;        }
    BoundType            get_type    (BoundRef bound_ref) const { return m_bounds[bound_ref].m_type;       }
    FormulaT             get_origin  (BoundRef bound_ref) const { return m_bounds[bound_ref].m_origin;     }
    bool                 is_derived  (BoundRef bound_ref) const { return m_bounds[bound_ref].m_is_derived; }
    bool                 is_active   (BoundRef bound_ref) const { return m_bounds[bound_ref].m_is_active;  }
    void                 activate    (BoundRef bound_ref)       { m_bounds[bound_ref].m_is_active = true;  }
    void                 deactivate  (BoundRef bound_ref)       { m_bounds[bound_ref].m_is_active = false; }

    bool is_below (const BoundRef l, const BoundRef u) const { return get_value(l) < get_value(u); }

/* ==================== Access and modification of a variable's information ==================== */

    bool        is_basic         (SimplexVariable v) const { return m_var_info[v].m_is_basic;      }
    bool        is_integer       (SimplexVariable v) const { return m_var_info[v].m_is_integer;    }
    bool        is_original      (SimplexVariable v) const { return m_var_info[v].m_is_original;   }
    std::size_t get_tableau_index(SimplexVariable v) const { return m_var_info[v].m_tableau_index; }
    
    void        set_basic         (SimplexVariable v, bool is_basic) { m_var_info[v].m_is_basic = is_basic; }
    void        set_tableau_index (SimplexVariable v, std::size_t i) { m_var_info[v].m_tableau_index = i;   }


/* ======================= Access and modification of a variable's range ======================= */

    bool has_lower_bound    (SimplexVariable v) const { return m_ranges[v].m_lower.has_value(); }
    bool has_upper_bound    (SimplexVariable v) const { return m_ranges[v].m_upper.has_value(); }
    BoundRef lower_bound    (SimplexVariable v) const { assert(has_lower_bound(v)); return *(m_ranges[v].m_lower); }
    BoundRef upper_bound    (SimplexVariable v) const { assert(has_upper_bound(v)); return *(m_ranges[v].m_upper); }
    void set_lower_unbounded(SimplexVariable v)       { m_ranges[v].m_lower = std::nullopt; }
    void set_upper_unbounded(SimplexVariable v)       { m_ranges[v].m_upper = std::nullopt; }
    void set_lower_bound    (SimplexVariable v, BoundRef bound_ref) { m_ranges[v].m_lower = bound_ref; }
    void set_upper_bound    (SimplexVariable v, BoundRef bound_ref) { m_ranges[v].m_upper = bound_ref; }

    bool has_consistent_range(SimplexVariable v) const {
        if (!(has_lower_bound(v) && has_upper_bound(v))) return true;
        return get_value(lower_bound(v)) <= get_value(upper_bound(v));
    }

    void update_range(const SimplexVariable v);
    bool update_range(const SimplexVariable v, const BoundRef b);

/* ===================================== Variable Creation ===================================== */

    SimplexVariable add_var(bool is_int, bool is_original) {
        SimplexVariable v = m_num_variables;
        ++m_num_variables;
        m_upper_bounds.emplace_back(m_ref_cmp);
        m_lower_bounds.emplace_back(m_ref_cmp);
        m_ranges.emplace_back();
        if constexpr (Settings::internal_neq_handling()){
            m_neq_bounds.emplace_back(m_ref_cmp);
        }
        m_var_info.emplace_back(is_int, is_original);
        m_tableau.ensure_var(v);
        return v;
    }

    void add_original_variable(const carl::Variable& v) {
        m_to_simplex_var.emplace(v, m_num_variables);
        bool is_int = (v.type() == carl::VariableType::VT_INT);
        add_var(is_int, /*is_orig: */ true);
    }

    SimplexVariable new_slack_variable(const Poly& lin_term) {
        SimplexVariable new_slack_var = add_var(/*is_int: */ false, /*is_orig: */ false);
        m_lhs_to_var.emplace(lin_term, new_slack_var);
        return new_slack_var;
    }

    void translate_variables(const FormulaT& f) {
        auto vars = f.variables();
        for (const auto& v : vars) {
            if (m_to_simplex_var.find(v) == m_to_simplex_var.end()) {
                add_original_variable(v);
            }
        }
    }

/* ======================================= Bound Creation ====================================== */

    bool find_conflicting_bounds(const SimplexVariable v, bool lower);
    void add_bound_to_sets(const BoundRef b);
    std::pair<SimplexVariable, Rational> add_to_tableau(const Poly& linear_term);

/* ================================== Assignment Initialization ================================ */

    bool violates_lower(const SimplexVariable v) const {
        return has_lower_bound(v) && (get_value(lower_bound(v)) > m_assignment[v]);
    }

    bool violates_upper(const SimplexVariable v) const {
        return has_upper_bound(v) && (get_value(upper_bound(v)) < m_assignment[v]);
    }

    bool assigned_in_range(const SimplexVariable v) const {
        return !(violates_lower(v) || violates_upper(v));
    }

    bool is_at_lower(const SimplexVariable v) const {
        if (!has_lower_bound(v)) return false;
        return m_assignment[v] == get_value(lower_bound(v));
    }

    bool is_at_upper(const SimplexVariable v) const {
        if (!has_upper_bound(v)) return false;
        return m_assignment[v] == get_value(upper_bound(v));
    }

    void compute_basic_assignment();
    void build_initial_assignment();

    void collect_nonbase() {
        assert(m_nonbase.empty());
        for (const auto& [_v, simplex_var] : m_to_simplex_var) {
            if (!is_basic(simplex_var)) m_nonbase.push_back(simplex_var);
        }
    }

/* ===================================== Conflict Handling ===================================== */

    void construct_infeasible_subset(const BoundVec& reason);

    bool exist_violated_bounds();

/* ========================================== Pivoting ========================================= */

    bool should_use_blands() const { return m_num_pivots > Settings::pivots_before_blands; }

    PivotCandidate choose_pivot        (const PivotCandidates& possible_pivots);
    PivotCandidate choose_pivot_bland  (const PivotCandidates& possible_pivots);
    PivotCandidate choose_pivot_heur   (const PivotCandidates& possible_pivots);
    PivotCandidate choose_pivot_fmplex (const PivotCandidates& possible_pivots);

    ConflictOrPivot         find_conflict_or_pivot();
    std::optional<BoundRef> check_suitable_for_pivot(const Tableau::Entry& entry,
                                                     const BoundRef b,
                                                     bool increase ) const;

    void pivot_and_update(PivotCandidate pivot_candidate);
    void update          (SimplexVariable nonbase_var, const DeltaRational& diff);
    void pivot           (SimplexVariable x_i, SimplexVariable x_j, const Rational& a_ij);


/* ======================================= NEQ Handling ======================================== */

    bool activate_neq   (const FormulaT& f);
    void deactivate_neq (const FormulaT& f);
    bool check_neqs     ();

/* ====================================== Bound Learning ======================================= */

    void learn_bounds();
    void derive_bounds(const Tableau::RowID rid);
    void derive_bound (const Tableau::RowID rid, const BoundType type);
    void add_derived_bound(const SimplexVariable var,
                           const BoundType type,
                           const DeltaRational& value,
                           const BoundVec& premises);

    void deactivate_bounds_derived_from(const FormulaT& f);
    bool reactivate_derived_bounds();

/* ===================================== Theory Propagation ==================================== */

    void simple_theory_propagation();

    void propagate(const BoundRef premise, const BoundRef conclusion, bool conclusion_negated);

    void propagate_lower(const BoundRef b);
    void propagate_upper(const BoundRef b);
    void propagate_equal(const BoundRef b);

};
}
