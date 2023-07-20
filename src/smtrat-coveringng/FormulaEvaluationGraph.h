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
struct CONSTRAINT { // TODO later: we add formulas like p<0 -> not p>0 and so on for all such constraint pairs
    carl::BasicConstraint<cadcells::Polynomial> constraint;
};

struct Formula {
    using Reasons = boost::container::flat_set<boost::container::flat_set<FormulaID>>;

    std::variant<TRUE,FALSE,NOT,AND,OR,IFF,XOR,BOOL,CONSTRAINT> content;
    boost::container::flat_set<FormulaID> parents;
    Reasons reasons_true;
    Reasons reasons_false;

    template<typename C>
    Formula(C&& c) : content(std::move(c)) {}

    Valuation valuation() {
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
    VariableToFormula vartof;
    boost::container::flat_set<FormulaID> conflicts;

    void propagate_consistency(FormulaID id);
    void propagate_root(FormulaID id, bool is_true);
    void evaluate(FormulaID id, const cadcells::Assignment& ass, carl::Variable main_var);
    void add_reasons_true(FormulaID id, const Formula::Reasons& reasons);
    void add_reasons_false(FormulaID id, const Formula::Reasons& reasons);
    Formula::Reasons conflict_reasons() const;
    void backtrack(FormulaID id);
};

}

class GraphEvaluation {

using ImplicantComplexityOrdering = std::function<bool(const boost::container::flat_set<cadcells::Constraint>&, const boost::container::flat_set<cadcells::Constraint>&)>;

private:
    formula_ds::FormulaGraph true_graph;
    formula_ds::FormulaGraph false_graph;
    cadcells::Assignment assignment;

    ImplicantComplexityOrdering m_implicant_complexity_ordering;
    std::size_t m_results;

public:
    GraphEvaluation(ImplicantComplexityOrdering implicant_complexity_ordering, std::size_t results) : m_implicant_complexity_ordering(implicant_complexity_ordering), m_results(results) {}

    void set_formula(typename cadcells::Polynomial::ContextType c, const FormulaT& f);
    void extend_valuation(const cadcells::Assignment& ass);
    void revert_valuation(const cadcells::Assignment& ass);
    std::vector<boost::container::flat_set<cadcells::Constraint>> compute_implicants() const;
    Valuation root_valuation() const;
};

}