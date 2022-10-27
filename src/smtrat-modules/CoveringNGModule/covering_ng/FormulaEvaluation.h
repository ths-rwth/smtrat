#pragma once

#include "types.h"
#include <memory>
#include <variant>

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
	std::unique_ptr<Content> m_content;
    
public:
    template<typename C>
    FormulaEvaluation(C&& c) : m_content(std::make_unique<Content>(std::move(c))) {};
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

// TODO later: introduce pool for formulas  (then in extend_valuation, we need to check if formula is already satisfied)
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
void extend_valuation(FormulaEvaluation& f, const cadcells::Assignment& ass);

void revert_valuation(FormulaEvaluation& f, std::size_t level);

void compute_implicant(const FormulaEvaluation& f, std::vector<cadcells::Constraint>& implicant);

FormulaEvaluation to_evaluation(typename cadcells::Polynomial::ContextType c, const FormulaT& f);

} // namespace smtrat::coveringng::formula

#include "FormulaEvaluationComplexity.h"
