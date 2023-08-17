#pragma once

#include "FormulaEvaluation.h"

#include <memory>
#include <variant>
#include <concepts>

namespace smtrat::covering_ng::formula {

namespace node_ds {

struct NodeContent;

class Node {
	std::shared_ptr<NodeContent> m_content;
    
public:
    Node(const Node& c) : m_content(c.m_content) {};
    template<typename C>
    requires (!std::same_as<C,Node> && !std::same_as<C,Node&>)
    Node(C&& c) : m_content(std::make_shared<NodeContent>(std::move(c))) {};
    inline const NodeContent& c() const { return *m_content; }
    inline NodeContent& c() { return *m_content; }
};

struct TRUE { };
struct FALSE { };
struct NOT { Node subformula; };
struct AND { std::vector<Node> subformulas; };
struct OR { std::vector<Node> subformulas; };
struct IFF { std::vector<Node> subformulas; };
struct XOR { std::vector<Node> subformulas; };
struct BOOL { carl::Variable variable; };
struct CONSTRAINT { carl::BasicConstraint<cadcells::Polynomial> constraint; };

struct NodeContent {
	std::variant<TRUE,FALSE,NOT,AND,OR,IFF,XOR,BOOL,CONSTRAINT> content;
    Valuation valuation;
    std::size_t max_level = 0;
    std::size_t max_degree = 0;
    std::size_t max_total_degree = 0;
    std::size_t num_subformulas = 0;
    std::size_t num_constraints = 0;
    carl::Variables boolean_variables;
    carl::Variables arithmetic_variables;

    template<typename C>
    NodeContent(C&& c) : content(std::move(c)), valuation(Valuation::UNKNOWN) {};
};

namespace complexity {
    
inline bool min_tdeg_ordering(const Node& a, const Node& b) {
    return a.c().max_total_degree < b.c().max_total_degree;
}

inline bool min_lvl_min_tdeg_ordering(const Node& a, const Node& b) {
    return a.c().max_level < b.c().max_level || (a.c().max_level == b.c().max_level && a.c().max_total_degree < b.c().max_total_degree);
}

}

}

class Minimal {
public:
    using FormulaComplexityOrdering = std::function<bool(const node_ds::Node&, const node_ds::Node&)>;

private:
    FormulaComplexityOrdering m_formula_complexity_ordering;
    std::optional<node_ds::Node> m_root;

public:
    Minimal(FormulaComplexityOrdering formula_complexity_ordering) : m_formula_complexity_ordering(formula_complexity_ordering) {}

    void set_formula(typename cadcells::Polynomial::ContextType c, const FormulaT& f);

    /**
     * @brief Updates the valuations. Assumes that ass is an extension of the previous assignment the formula has been evaluated with.
     * 
     * @param f 
     * @param ass 
     */
    void extend_valuation(const cadcells::Assignment& ass);
    void revert_valuation(const cadcells::Assignment& ass);
    std::vector<boost::container::flat_set<cadcells::Constraint>> compute_implicants() const;
    Valuation root_valuation() const;
};

class ExhaustiveImplicants {
private:
    ImplicantOrdering m_implicant_complexity_ordering;
    std::size_t m_results;
    std::size_t m_pruning;
    std::optional<node_ds::Node> m_root;

public:
    ExhaustiveImplicants(ImplicantOrdering implicant_complexity_ordering) : m_implicant_complexity_ordering(implicant_complexity_ordering), m_results(0), m_pruning(0) {}
    ExhaustiveImplicants(ImplicantOrdering implicant_complexity_ordering, std::size_t results) : m_implicant_complexity_ordering(implicant_complexity_ordering), m_results(results), m_pruning(0) {}
    ExhaustiveImplicants(ImplicantOrdering implicant_complexity_ordering, std::size_t results, std::size_t pruning) : m_implicant_complexity_ordering(implicant_complexity_ordering), m_results(results), m_pruning(pruning) {}

    void set_formula(typename cadcells::Polynomial::ContextType c, const FormulaT& f);
    void extend_valuation(const cadcells::Assignment& ass);
    void revert_valuation(const cadcells::Assignment& ass);
    std::vector<boost::container::flat_set<cadcells::Constraint>> compute_implicants() const;
    Valuation root_valuation() const;
};

} // namespace smtrat::coveringng::formula