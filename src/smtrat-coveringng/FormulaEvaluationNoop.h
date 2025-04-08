#pragma once

#include "FormulaEvaluation.h"

namespace smtrat::covering_ng::formula {

namespace formula_noop_ds {

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
    Valuation value = Valuation::MULTIVARIATE;
    template<typename C>
    Formula(const C& c) : content(c) {}
};

using FormulaDB = std::vector<Formula>;
using VariableToFormula = boost::container::flat_map<carl::Variable, std::vector<FormulaID>>;
struct FormulaTree {
    FormulaDB db;
    FormulaID root;
    VariableToFormula vartof;
    void propagate_consistency(FormulaID id);
};

}

class NoopEvaluation {
    cadcells::datastructures::Projections& m_proj;
    formula_noop_ds::FormulaTree formula;
    cadcells::Assignment assignment;
    ConstraintOrdering m_constraint_complexity_ordering;

public:
    NoopEvaluation(cadcells::datastructures::Projections& proj, ConstraintOrdering constraint_complexity_ordering) : m_proj(proj), m_constraint_complexity_ordering(constraint_complexity_ordering) {}

    void set_formula(const FormulaT& f);
    void extend_valuation(const cadcells::Assignment& ass);
    void revert_valuation(const cadcells::Assignment& ass);
    std::vector<Implicant> compute_implicants();
    Valuation root_valuation() const;
};

}