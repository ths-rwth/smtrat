#pragma once

#include "FormulaEvaluation.h"

namespace smtrat::covering_ng::formula {

namespace formula_ds {

using FormulaID = std::size_t;

struct TRUE {};
struct FALSE {};
struct NOT {
    FormulaID subformula;
};
struct AND {
    std::vector<FormulaID> subformulas;
};
struct OR {
    std::vector<FormulaID> subformulas;
};
struct IFF {
    std::vector<FormulaID> subformulas;
};
struct XOR {
    std::vector<FormulaID> subformulas;
};
struct BOOL {
    carl::Variable variable;
};
struct CONSTRAINT {
    carl::BasicConstraint<cadcells::Polynomial> constraint;
};

struct Formula {
    using Reason = boost::container::flat_set<std::pair<FormulaID,bool>>;
    using Reasons = boost::container::flat_set<Reason>;

    std::variant<TRUE,FALSE,NOT,AND,OR,IFF,XOR,BOOL,CONSTRAINT> content;
    boost::container::flat_set<FormulaID> parents;
    Reasons reasons_true;
    Reasons reasons_false;

    template<typename C>
    Formula(const C& c) : content(c) {}

    Valuation valuation() const {
        if (reasons_true.empty() && reasons_false.empty()) return Valuation::MULTIVARIATE;
        else if (reasons_true.empty()) return Valuation::FALSE;
        else if (reasons_false.empty()) return Valuation::TRUE;
        else return Valuation::UNKNOWN; // conflict
    }
};

using FormulaDB = std::vector<Formula>;
using VariableToFormula = boost::container::flat_map<carl::Variable, boost::container::flat_set<FormulaID>>;

struct FormulaGraph {
    FormulaDB db;
    FormulaID root;
    boost::container::flat_set<FormulaID> conflicts;

    void propagate_consistency(FormulaID id);
    void propagate_root(FormulaID id, bool is_true);
    void propagate_decision(FormulaID id, bool is_true);
    void add_reasons_true(FormulaID id, const Formula::Reasons& reasons);
    void add_reasons_false(FormulaID id, const Formula::Reasons& reasons);
    Formula::Reasons conflict_reasons() const;
    void backtrack(FormulaID id, bool is_true);
};

}

class GraphEvaluation {

private:
    formula_ds::FormulaGraph true_graph;
    formula_ds::FormulaGraph false_graph;
    formula_ds::VariableToFormula vartof;
    cadcells::Assignment assignment;
    boost::container::flat_map<formula_ds::FormulaID, bool> m_decisions;
    formula_ds::Formula::Reasons m_true_conflict_reasons;
    formula_ds::Formula::Reasons m_false_conflict_reasons;

    ImplicantOrdering m_implicant_complexity_ordering;
    std::size_t m_results;
    ConstraintOrdering m_constraint_complexity_ordering;
    bool m_stop_evaluation_on_conflict;
    bool m_preprocess;
    bool m_postprocess;
    bool m_boolean_check;
    bool m_boolean_check_only_bool;

    formula_ds::Formula::Reasons explore(formula_ds::FormulaGraph& graph); 

public:
    GraphEvaluation(ImplicantOrdering implicant_complexity_ordering, std::size_t results, ConstraintOrdering constraint_complexity_ordering, bool stop_evaluation_on_conflict, bool preprocess, bool postprocess, bool boolean_check, bool boolean_check_only_bool = false) : m_implicant_complexity_ordering(implicant_complexity_ordering), m_results(results), m_constraint_complexity_ordering(constraint_complexity_ordering), m_stop_evaluation_on_conflict(stop_evaluation_on_conflict), m_preprocess(preprocess), m_postprocess(postprocess), m_boolean_check(boolean_check), m_boolean_check_only_bool(boolean_check_only_bool) {}

    void set_formula(typename cadcells::Polynomial::ContextType c, const FormulaT& f);
    void extend_valuation(const cadcells::Assignment& ass);
    void revert_valuation(const cadcells::Assignment& ass);
    std::vector<boost::container::flat_set<cadcells::Constraint>> compute_implicants() const;
    Valuation root_valuation() const;
};

}