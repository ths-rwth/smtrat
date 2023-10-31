#pragma once

#include <smtrat-common/smtrat-common.h>

namespace smtrat::qe::util {

class EquationSubstitution {
private:
    FormulasT m_constraints;
    std::vector<carl::Variable> m_variables;

public:
    EquationSubstitution(const FormulasT& cs, const std::vector<carl::Variable>& vs)
    : m_constraints(cs), m_variables(vs) {}

    EquationSubstitution(FormulasT&& cs, std::vector<carl::Variable>&& vs)
    : m_constraints(std::move(cs)), m_variables(std::move(vs)) {}

    bool apply() {
        SMTRAT_LOG_DEBUG("smtrat.qe","begin");

        auto first_ineq = std::partition(
            m_constraints.begin(),
            m_constraints.end(),
            [](const auto& c) { return c.constraint().relation() == carl::Relation::EQ; }
        );

        FormulasT done;
        for (auto eq_it = m_constraints.begin(); eq_it != first_ineq; ++eq_it) {
            Poly lhs = eq_it->constraint().lhs();
            assert(lhs.is_linear());
            std::optional<TermT> subst_term = std::nullopt;
            for (const auto& term: lhs) {
                if (term.is_constant()) continue;
                auto it = std::find(m_variables.begin(), m_variables.end(), term.single_variable());
                if (it != m_variables.end()) {
                    subst_term = term;
                    m_variables.erase(it);
                    break;
                }
            }
            if (!subst_term) {
                done.push_back(*eq_it);
                continue;
            }
            // replace in all remaining equations and other constraints
            Poly subst = (Poly(*subst_term) - lhs)/(subst_term->coeff());
            std::for_each(std::next(eq_it), m_constraints.end(), [&subst_term, &subst](auto& c){
                Poly other_lhs = c.constraint().lhs();
                carl::substitute_inplace(other_lhs, subst_term->single_variable(), subst);
                c = FormulaT(other_lhs, c.constraint().relation());
            });
        }
        done.insert(done.end(), first_ineq, m_constraints.end());
        for (const auto& c : done) {
            if (c.constraint().is_consistent() == 0) {
                m_constraints.clear();
                m_variables.clear();
                SMTRAT_LOG_DEBUG("smtrat.qe","end false");
                return false;
            }
        }

        m_constraints = done;
        SMTRAT_LOG_DEBUG("smtrat.qe","end true");
        return true;
    }

    std::vector<carl::Variable> remaining_variables() {
        return m_variables;
    }

    FormulasT remaining_constraints() {
        return m_constraints;
    }

};

}