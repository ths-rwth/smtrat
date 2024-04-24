#pragma once

#include <smtrat-common/smtrat-common.h>

namespace smtrat::qe::util {

struct VariableIndex {
    std::vector<carl::Variable> m_vars;

    VariableIndex() {}


    explicit VariableIndex(const std::vector<carl::Variable>& vs) : m_vars(vs) {}

    std::size_t add_variable(const carl::Variable v) {
        if (std::find(m_vars.begin(), m_vars.end(), v) == m_vars.end()) {
            m_vars.push_back(v);
        }
        return m_vars.size() - 1;
    }

    void gather_variables(const FormulasT& fs) {
        carl::carlVariables vs;
        for (const auto& f : fs) carl::variables(f, vs);
        for (const auto  v : vs) add_variable(v);
    }

    std::size_t index(carl::Variable v) const {
        auto it = std::find(m_vars.begin(), m_vars.end(), v);
        assert(it != m_vars.end());
        return std::distance(m_vars.begin(), it);
    }
    carl::Variable var(std::size_t i) const {
        assert(i < m_vars.size());
        return m_vars[i];
    }

    std::size_t size() const { return m_vars.size(); }
};
    
}