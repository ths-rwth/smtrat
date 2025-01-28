#pragma once

#include "FormulaEvaluation.h"

namespace smtrat::covering_ng::formula {

namespace formula_ds {

// using FormulaID = std::size_t;
using FormulaID = unsigned;

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
    cadcells::datastructures::PolyConstraint constraint;
};

struct Formula {
    std::variant<TRUE,FALSE,NOT,AND,OR,IFF,XOR,BOOL,CONSTRAINT> content;
    boost::container::flat_set<FormulaID> parents;
    template<typename C>
    Formula(const C& c) : content(c) {}
};

using FormulaDB = std::vector<Formula>;
using VariableToFormula = boost::container::flat_map<carl::Variable, std::vector<FormulaID>>;
struct FormulaTree {
    FormulaDB db;
    FormulaID root;
    VariableToFormula vartof;
};

struct FormulaState {
    using Reason = std::vector<std::pair<FormulaID,bool>>;
    using Reasons = std::vector<Reason>;

    Reasons reasons_true;
    Reasons reasons_false;
};

struct FormulaTreeState {
    std::shared_ptr<FormulaTree> formula;
    std::vector<FormulaState> states;
    boost::container::flat_set<FormulaID> conflicts;

    bool downwards_propagation;

    Valuation valuation(FormulaID id) const {
        if (states.at(id).reasons_true.empty() && states.at(id).reasons_false.empty()) return Valuation::MULTIVARIATE;
        else if (states.at(id).reasons_true.empty()) return Valuation::FALSE;
        else if (states.at(id).reasons_false.empty()) return Valuation::TRUE;
        else return Valuation::UNKNOWN; // conflict
    }

    void propagate_consistency(FormulaID id);
    void propagate_root(FormulaID id, bool is_true);
    void propagate_decision(FormulaID id, bool is_true);
    void add_reasons_true(FormulaID id, const FormulaState::Reasons& reasons);
    void add_reasons_false(FormulaID id, const FormulaState::Reasons& reasons);
    FormulaState::Reasons conflict_reasons() const;
    void backtrack(FormulaID id, bool is_true);
};

}

class GraphEvaluation {

public:
    enum BooleanExploration { OFF, PROPAGATION, EXPLORATION, EXPLORATION_ONLY_BOOL };

private:
    cadcells::datastructures::Projections& m_proj;

    formula_ds::FormulaTreeState true_graph;
    formula_ds::FormulaTreeState false_graph;
    cadcells::Assignment assignment;
    boost::container::flat_map<formula_ds::FormulaID, bool> m_decisions;
    formula_ds::FormulaState::Reasons m_true_conflict_reasons;
    formula_ds::FormulaState::Reasons m_false_conflict_reasons;

    ImplicantOrdering m_implicant_complexity_ordering;
    std::size_t m_results;
    ConstraintOrdering m_constraint_complexity_ordering;
    bool m_stop_evaluation_on_conflict;
    bool m_preprocess;
    bool m_postprocess;
    BooleanExploration m_boolean_exploration;

    formula_ds::FormulaState::Reasons explore(formula_ds::FormulaTreeState& graph); 

public:
    GraphEvaluation(cadcells::datastructures::Projections& proj, ImplicantOrdering implicant_complexity_ordering, std::size_t results, ConstraintOrdering constraint_complexity_ordering, bool stop_evaluation_on_conflict, bool preprocess, bool postprocess, BooleanExploration boolean_exploration) : m_proj(proj), m_implicant_complexity_ordering(implicant_complexity_ordering), m_results(results), m_constraint_complexity_ordering(constraint_complexity_ordering), m_stop_evaluation_on_conflict(stop_evaluation_on_conflict), m_preprocess(preprocess), m_postprocess(postprocess), m_boolean_exploration(boolean_exploration) {}

    void set_formula(const FormulaT& f);
    void extend_valuation(const cadcells::Assignment& ass);
    void revert_valuation(const cadcells::Assignment& ass);
    std::vector<Implicant> compute_implicants();
    Valuation root_valuation() const;
};

}