#pragma once

#include <smtrat-common/smtrat-common.h>

namespace smtrat::qe::util {

struct Subquery {
    FormulasT constraints;
    std::vector<carl::Variable> elimination_vars;
    Subquery(const FormulasT& fs, const std::vector<carl::Variable> vs)
    : constraints(fs), elimination_vars(vs) {}
};

std::vector<Subquery> split_quantifiers(const FormulasT& constraints, const std::vector<carl::Variable>& vars) {
    std::vector<Subquery> blocks;
    std::vector<int> ccs(vars.size(), -1);
    std::vector<bool> constraint_used(constraints.size(), false);
    
    std::vector<std::size_t> pending;

    for (std::size_t i = 0; i < vars.size();) {
        pending.push_back(i);
        blocks.push_back(Subquery({},{}));
        ++i;
        while (!pending.empty()) {
            std::size_t v = pending.back();
            pending.pop_back();
            if (ccs[v] != -1) continue;
            assert(blocks.size() > 0);
            ccs[v] = static_cast<int>(blocks.size()) - 1;
            blocks.back().elimination_vars.push_back(vars[v]);
            for (std::size_t k = 0; k < constraints.size(); ++k) {
                if (constraint_used[k]) continue;
                auto vars_c = carl::variables(constraints[k]);
                if (vars_c.has(vars[v])) {
                    for (std::size_t v_other = 0; v_other < vars.size(); ++v_other) {
                        if (v != v_other && vars_c.has(vars[v_other])) {
                            pending.push_back(v_other);
                        }
                    }
                    constraint_used[k] = true;
                    blocks.back().constraints.push_back(constraints[k]);
                }
            }
        }
        while (i < vars.size() && ccs[i] != -1) ++i;
    }

    return blocks;
}

}