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
#include "SimplexStatistics.h"

namespace smtrat {

template<typename Settings>
class SimplexModule : public Module {

/* ============================================================================================= */
/* //////////////////////////////////    Type Definitions    /////////////////////////////////// */
/* ============================================================================================= */
private:
    using DeltaRational = simplex::DeltaValue<Rational>;
    using Tableau       = simplex::Tableau<Rational>;

    using Bound         = simplex::Bound<DeltaRational>;
    using BoundType     = simplex::BoundType;
    using Bounds        = simplex::Bounds<DeltaRational>;
    using BoundRef      = Bounds::Ref;
    using BoundSet      = BoundRef::Set;
    using BoundVec      = std::vector<BoundRef>;

    using VarIndex      = std::map<carl::Variable, simplex::Variable>;

    /**
     * The range (lower bound, upper bound) of a variable.
     * If a bound is nullopt, then the respective side is unbounded.
     */
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
        simplex::Variable     m_basic_var;
        const Tableau::Entry& mr_nonbasic;

        simplex::Variable basic_var   () const { return m_basic_var; }
        simplex::Variable nonbasic_var() const { return mr_nonbasic.var(); }
        Rational          coeff       () const { return mr_nonbasic.coeff(); }

        PivotCandidate(simplex::Variable v, const Tableau::Entry& e)
        : m_basic_var(v), mr_nonbasic(e) {}
    };

    using PivotCandidates = std::map<simplex::Variable, std::vector<const Tableau::Entry*>>;

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

    // Information about variables
    std::size_t                        m_num_variables = 0;
    VarIndex                           m_to_simplex_var;
    std::vector<simplex::VariableInfo> m_var_info;

    // working assignment
    std::vector<DeltaRational>         m_assignment;
    mutable bool                       m_model_computed = false;

    // Tableau data
    Tableau                            m_tableau;
    std::vector<simplex::Variable>     m_base;        // = map : Tableau::RowID -> simplex::Variable
    std::vector<Rational>              m_base_coeffs; // = map : Tableau::RowID -> Rational
    std::vector<simplex::Variable>     m_nonbase;
    // TODO: use nonbase? we can store a variable's index in the nonbase in tableau_index (rename)
    // build_initial_assignment could be made more efficient with that.
    std::map<Poly, simplex::Variable>  m_lhs_to_var;  // slack variable transformation

    // Information for pivoting
    std::size_t                        m_num_pivots = 0;
    std::set<simplex::Variable>        m_changed_basic_vars; // basic vars which might be violated

    // Stored bounds
    Bounds                             m_bounds;          // owns the bounds
    std::vector<BoundSet>              m_lower_bounds;
    std::vector<BoundSet>              m_upper_bounds;
    std::vector<Range>                 m_ranges;
    BoundVec                           m_violated_bounds; // temporary storage
    BoundRef::cmp                      m_ref_cmp;         // needed for ordering BoundRefs in sets
    BoundVec                           m_derived_bounds;
    std::map<FormulaT, BoundVec>       m_bounds_derived_from;

    // NEQHandling
    FormulasT                          m_neq_constraints; // used by SPLITTING_ON_DEMAND
    std::vector<BoundSet>              m_neq_bounds;      // used by UPDATE_PERTURBATION and PIVOT

    #ifdef SMTRAT_DEVOPTION_Statistics
    SimplexStatistics& m_statistics = statistics_get<SimplexStatistics>("Simplex");
    #endif

/* ============================================================================================= */
/* //////////////////////////////////    Public Interfaces    ////////////////////////////////// */
/* ============================================================================================= */
public:

    SimplexModule(const ModuleInput*, Conditionals&, Manager* = nullptr);

    ~SimplexModule();


    typedef Settings SettingsType;
    std::string moduleName() const { return SettingsType::moduleName; }

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

    Answer process_result(Answer a) {
        #ifdef SMTRAT_DEVOPTION_Statistics
            m_statistics.check(rReceivedFormula());
            m_statistics.tableau_entries(m_tableau.num_entries());
            m_statistics.tableau_size(m_tableau.num_rows()*m_tableau.num_vars());
        #endif
        if (a == Answer::SAT) {
            m_model_computed = false;
            updateModel();

            if constexpr (Settings::neq_handling == simplex::NEQHandling::SPLITTING_ON_DEMAND) {
                if (!check_neqs()) return Answer::UNKNOWN;
            }
        } else {
            assert(a == Answer::UNSAT);
            SMTRAT_STATISTICS_CALL(m_statistics.conflict(mInfeasibleSubsets));
        }
        return a;
    }

/* ============================= Access to Bound data via BoundRef ============================= */

    const DeltaRational& get_value   (BoundRef b) const { return m_bounds[b].m_value;      }
    simplex::Variable    get_variable(BoundRef b) const { return m_bounds[b].m_var;        }
    BoundType            get_type    (BoundRef b) const { return m_bounds[b].m_type;       }
    FormulaT             get_origin  (BoundRef b) const { return m_bounds[b].m_origin;     }
    bool                 is_derived  (BoundRef b) const { return m_bounds[b].m_is_derived; }
    bool                 is_active   (BoundRef b) const { return m_bounds[b].m_is_active;  }
    void                 activate    (BoundRef b)       { m_bounds[b].m_is_active = true;  }
    void                 deactivate  (BoundRef b)       { m_bounds[b].m_is_active = false; }

    bool is_below (const BoundRef l, const BoundRef u) const { return get_value(l) < get_value(u); }

/* ==================== Access and modification of a variable's information ==================== */

    bool        is_basic      (simplex::Variable v) const { return m_var_info[v].m_is_basic;      }
    bool        is_integer    (simplex::Variable v) const { return m_var_info[v].m_is_integer;    }
    bool        is_original   (simplex::Variable v) const { return m_var_info[v].m_is_original;   }
    std::size_t tableau_index (simplex::Variable v) const { return m_var_info[v].m_tableau_index; }
    
    void        set_basic         (simplex::Variable v, bool is_basic) { m_var_info[v].m_is_basic = is_basic; }
    void        set_tableau_index (simplex::Variable v, std::size_t i) { m_var_info[v].m_tableau_index = i;   }

/* ======================= Access and modification of a variable's range ======================= */

    bool has_lower_bound    (simplex::Variable v) const { return m_ranges[v].has_lower(); }
    bool has_upper_bound    (simplex::Variable v) const { return m_ranges[v].has_upper(); }
    BoundRef lower_bound    (simplex::Variable v) const { return m_ranges[v].lower(); }
    BoundRef upper_bound    (simplex::Variable v) const { return m_ranges[v].upper(); }
    void set_lower_unbounded(simplex::Variable v)       { m_ranges[v].m_lower = std::nullopt; }
    void set_upper_unbounded(simplex::Variable v)       { m_ranges[v].m_upper = std::nullopt; }
    void set_lower_bound    (simplex::Variable v, BoundRef b) { m_ranges[v].m_lower = b; }
    void set_upper_bound    (simplex::Variable v, BoundRef b) { m_ranges[v].m_upper = b; }

    bool has_consistent_range(simplex::Variable v) const {
        if (!has_lower_bound(v) || !has_upper_bound(v)) return true;
        return get_value(lower_bound(v)) <= get_value(upper_bound(v));
    }

    /**
     * @brief Sets the given variable's range to the strictest active bounds.
     * @param v the variable whose range is updated.
     */
    void update_range(const simplex::Variable v);

    /**
     * @brief Updates the given variable's range using the given bound.
     * @param v the variable whose range is updated.
     * @param b the bound to consider as new lower or upper bound
     * @return false if the updated range is inconsistent, and true otherwise
     */
    bool update_range(const simplex::Variable v, const BoundRef b);

/* ===================================== Variable Creation ===================================== */

    simplex::Variable add_var(bool is_int, bool is_original) {
        simplex::Variable v = m_num_variables;
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

    simplex::Variable new_slack_variable(const Poly& lin_term) {
        simplex::Variable new_slack_var = add_var(/*is_int: */ false, /*is_orig: */ false);
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

    /**
     * Looks for conflicts between the given upper bound on v and v's active lower bounds.
     * All found conflicts are stored as infeasible subsets in mInfeasibleSubsets.
     * @returns true if at least one conflict was found
     */
    bool find_conflicting_lower_bounds(const simplex::Variable v, BoundRef b);

    /**
     * Looks for conflicts between the given lower bound on v and v's active upper bounds.
     * All found conflicts are stored as infeasible subsets in mInfeasibleSubsets.
     * @returns true if at least one conflict was found
     */
    bool find_conflicting_upper_bounds(const simplex::Variable v, BoundRef b);

    /**
     * Adds the given BoundRef to the respective member sets (m_lower_bounds, m_upper_bounds, ...).
     */
    void add_bound_to_sets(const BoundRef b);

    /**
     * Adds a given linear term to m_tableau.
     * If there already is a slack variable for this term (or a colinear one), nothing is added.
     * @returns the corresponding slack variable s and a factor c so that c*s = linear_term.
     */
    std::pair<simplex::Variable, Rational> add_to_tableau(const Poly& linear_term);

/* ============================= Assignment Check and Initialization =========================== */

    bool violates_lower(const simplex::Variable v) const {
        return has_lower_bound(v) && (get_value(lower_bound(v)) > m_assignment[v]);
    }

    bool violates_upper(const simplex::Variable v) const {
        return has_upper_bound(v) && (get_value(upper_bound(v)) < m_assignment[v]);
    }

    bool assigned_in_range(const simplex::Variable v) const {
        return !(violates_lower(v) || violates_upper(v));
    }

    bool is_at_lower(const simplex::Variable v) const {
        return has_lower_bound(v) && (m_assignment[v] == get_value(lower_bound(v)));
    }

    bool is_at_upper(const simplex::Variable v) const {
        return has_upper_bound(v) && (m_assignment[v] == get_value(upper_bound(v)));
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
    void update          (simplex::Variable nonbase_var, const DeltaRational& diff);
    void pivot           (simplex::Variable x_i, simplex::Variable x_j, const Rational& a_ij);


/* ======================================= NEQ Handling ======================================== */

    bool activate_neq   (const FormulaT& f);
    void deactivate_neq (const FormulaT& f);
    bool check_neqs     ();

/* ====================================== Bound Learning ======================================= */

    /*
     * Derives bounds from a row of the tableau using existing bounds on the involved variables.
     * If s = a_1*x_1 + ... + a_n*x_n (chosen so that a_i != 0 for all i) and for each i holds 
     * (a_i < 0 => x_i has a lower bound c_i) and (a_i > 0 => x_i has an upper bound c_i), then
     * we can derive s >= a_1*c_1 + ... + a_n*c_n, possibly stronger than an existing bound on s.
     * Exchanging lower and upper bounds allows to derive upper bounds on s.
     */
    void derive_bounds(const Tableau::RowID rid);
    void derive_bound (const Tableau::RowID rid, const BoundType type);
    void add_derived_bound(const simplex::Variable var,
                           const BoundType type,
                           const DeltaRational& value,
                           const BoundVec& premises);

    void propagate_derived_lower(const simplex::Variable v, const BoundRef b);
    void propagate_derived_upper(const simplex::Variable v, const BoundRef b);

    void deactivate_bounds_derived_from(const FormulaT& f);
    bool reactivate_derived_bounds();

/* ===================================== Theory Propagation ==================================== */

    /*
     * Passes to a preceding SATModule theory lemmas of the following form, where x is a variable:
     * 
     * x <= c (or x = c) implies          x >= c (or x = c) implies             
     *         x <= d      if c <= d              x >= d      if c >= d
     *         not(x >= d) if c <  d              not(x <= d) if c >  d
     *         not(x =  d) if c <  d              not(x =  d) if c <  d
     * 
     * Notice that these simple bounds are translated back to original constraints for this.
     */
    void simple_theory_propagation();

    void propagate         (const BoundRef premise, const BoundRef conclusion);
    void propagate_negated (const BoundRef premise, const BoundRef conclusion);

    void propagate_lower(const BoundRef b);
    void propagate_upper(const BoundRef b);
    void propagate_equal(const BoundRef b);

};
}
