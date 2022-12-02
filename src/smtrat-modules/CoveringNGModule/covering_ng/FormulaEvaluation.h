#pragma once

#include "types.h"
#include <memory>
#include <variant>
#include <concepts>

namespace smtrat::covering_ng::formula {

struct Content;

enum class Valuation {
    TRUE, FALSE, MULTIVARIATE, UNKNOWN 
};
inline std::ostream& operator<<(std::ostream& o, Valuation v) {
    if (v == Valuation::TRUE)  o << "TRUE";
    else if (v == Valuation::FALSE)  o << "FALSE";
    else if (v == Valuation::MULTIVARIATE)  o << "MULTIVARIATE";
    else o << "UNKNOWN";
    return o;
}

class FormulaEvaluation {
	std::shared_ptr<Content> m_content;
    
public:
    FormulaEvaluation(const FormulaEvaluation& c) : m_content(c.m_content) {};
    template<typename C>
    requires (!std::same_as<C,FormulaEvaluation> && !std::same_as<C,FormulaEvaluation&>)
    FormulaEvaluation(C&& c) : m_content(std::make_shared<Content>(std::move(c))) {};
    inline const Content& c() const { return *m_content; }
    inline Content& c() { return *m_content; }
};

struct TRUE { };
struct FALSE { };
struct NOT { FormulaEvaluation subformula; };
struct AND { std::vector<FormulaEvaluation> subformulas; };
struct OR { std::vector<FormulaEvaluation> subformulas; };
struct IFF { std::vector<FormulaEvaluation> subformulas; };
struct XOR { std::vector<FormulaEvaluation> subformulas; };
struct BOOL { carl::Variable variable; };
struct CONSTRAINT { carl::BasicConstraint<cadcells::Polynomial> constraint; };

struct Content {
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
    Content(C&& c) : content(std::move(c)), valuation(Valuation::UNKNOWN) {};
};

void sort_by_complexity(FormulaEvaluation& f, const std::function<bool(const FormulaEvaluation&, const FormulaEvaluation&)>& compare);

/**
 * @brief Updates the valuations. Assumes that ass is an extension of the previous assignment the formula has been evaluated with.
 * 
 * @param f 
 * @param ass 
 */
void extend_valuation(FormulaEvaluation& f, const cadcells::Assignment& ass, bool evaluate_all = false);

void revert_valuation(FormulaEvaluation& f, std::size_t level);

void compute_implicant(const FormulaEvaluation& f, boost::container::flat_set<cadcells::Constraint>& implicant);

void compute_implicant(const FormulaEvaluation& f, boost::container::flat_set<cadcells::Constraint>& implicant, const std::function<bool(const boost::container::flat_set<cadcells::Constraint>&, const boost::container::flat_set<cadcells::Constraint>&)>& compare);

FormulaEvaluation to_evaluation(typename cadcells::Polynomial::ContextType c, const FormulaT& f);

// TODO this is a hack
struct FormulaEvaluationWrapper {
    FormulaEvaluation m_eval;
    bool m_exhaustive_implicant_computation;
    std::function<bool(const FormulaEvaluation&, const FormulaEvaluation&)> m_formula_complexity_ordering;
    std::function<bool(const boost::container::flat_set<cadcells::Constraint>&, const boost::container::flat_set<cadcells::Constraint>&)> m_implicant_complexity_ordering;

    inline void init() {
        if (m_exhaustive_implicant_computation)
            sort_by_complexity(m_eval, m_formula_complexity_ordering);
    }
    inline const Content& c() const { return m_eval.c(); }
    inline Content& c() { return m_eval.c(); }
};
inline void extend_valuation(FormulaEvaluationWrapper& f, const cadcells::Assignment& ass) {
    return extend_valuation(f.m_eval, ass, f.m_exhaustive_implicant_computation);
}
inline void revert_valuation(FormulaEvaluationWrapper& f, std::size_t level) {
    return revert_valuation(f.m_eval, level);
}
inline void compute_implicant(const FormulaEvaluationWrapper& f, boost::container::flat_set<cadcells::Constraint>& implicant) {
    if (!f.m_exhaustive_implicant_computation) return compute_implicant(f.m_eval, implicant);
    else return compute_implicant(f.m_eval, implicant, f.m_implicant_complexity_ordering);
}



} // namespace smtrat::coveringng::formula

#include "FormulaEvaluationComplexity.h"
