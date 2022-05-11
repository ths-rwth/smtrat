/**
 * @file UnionFindModule.cpp
 * @author Henrich Lauko <xlauko@mail.muni.cz>
 * @author Dominika Krejci <dominika.krejci@rwth-aachen.de>
 *
 * @version 2018-11-18
 * Created on 2018-11-18.
 */

#include "UnionFindModule.h"
#include "UnionFind.h"

#include <carl-formula/uninterpreted/UFInstanceManager.h>
#include <carl-formula/uninterpreted/SortValueManager.h>

namespace smtrat
{
    template<class Settings>
    UnionFindModule<Settings>::UnionFindModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
        Module( _formula, _conditionals, _manager )
        , classes(translate)
    {
    }

    template<class Settings>
    UnionFindModule<Settings>::~UnionFindModule()
    {}

    // eq_diamond16.smt2  3.23s user 0.01s system 99% cpu 3.244 total

    template<class Settings>
    bool UnionFindModule<Settings>::informCore( const FormulaT& _constraint )
    {
        assert(_constraint.type() == carl::UEQ);
        const auto& ueq = _constraint.u_equality();
        assert(ueq.lhs().isUVariable() && ueq.rhs().isUVariable());

        auto process = [&] (const auto& var) {
            if (const auto& [it, inserted] = variables.emplace(var); inserted) {
                need_to_update = true;
                graph.add_vertex(var);
            }
        };

        const auto& lhs = ueq.lhs().asUVariable();
        const auto& rhs = ueq.rhs().asUVariable();

        process(lhs);
        process(rhs);

        if constexpr (Settings::use_theory_propagation) {
            informed.emplace(lhs, rhs, false);
        }

        if (ueq.negated()) {
            if (lhs == rhs)
                return false;
        }

        return true;
    }

    template<class Settings>
    bool UnionFindModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        if (need_to_update) {
            classes.init(variables);
            need_to_update = false;
        }

        assert(_subformula->formula().type() == carl::UEQ);
        const auto& ueq = _subformula->formula().u_equality();
        assert(ueq.lhs().isUVariable() && ueq.rhs().isUVariable());

        const auto& lhs = ueq.lhs().asUVariable();
        const auto& rhs = ueq.rhs().asUVariable();

        if (!ueq.negated()) {
            assert(classes.has_variable(lhs) && classes.has_variable(rhs));
            classes.merge(lhs, rhs);
            graph.add_edge(lhs, rhs); //try to add in inform core

            if constexpr (Settings::use_theory_propagation) {
                if (informed.count(ueq))
                    informed.erase(ueq);
            }
        }

        history.emplace_back(ueq);

        return true;
    }

    template<class Settings>
    void UnionFindModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        assert(_subformula->formula().type() == carl::UEQ);
        const auto& ueq = _subformula->formula().u_equality();

        auto it = std::find(history.rbegin(), history.rend(), ueq);

        if (!it->negated()) {
            const auto& lhs = it->lhs().asUVariable();
            const auto& rhs = it->rhs().asUVariable();
            classes.backtrack(lhs, rhs);

            graph.remove_edge(lhs, rhs);

            // TODO optimize - reinsert after last removeCore call
            // reinsert history tail
            if (it != history.rbegin()) {
                History tail;
                for (auto eq = it.base(); eq != history.end(); ++eq) {
                    const auto& a = eq->lhs().asUVariable();
                    const auto& b = eq->rhs().asUVariable();
                    assert(classes.has_variable(a));
                    assert(classes.has_variable(b));
                    if (!eq->negated()) {
                        classes.merge(a, b);
                    }
                }
            }
        }

        history.erase(std::next(it).base());
    }

    template<class Settings>
    void UnionFindModule<Settings>::updateModel() const
    {
        using Class = typename decltype(classes)::Representative;
        std::unordered_map<Class, carl::SortValue> sorts;

        mModel.clear();
        if( solverState() == Answer::SAT )
        {
            for (const auto& var : variables) {
                auto cls = classes.find(var);

                if (!sorts.count(cls)) {
                    sorts[cls] = carl::newSortValue(var.domain());
                }

                mModel.emplace(var, sorts[cls]);
            }
        }
    }

    template<typename Settings>
    void UnionFindModule<Settings>::generateInfeasibleSubset(const carl::UEquality& inequality)
    {
        mInfeasibleSubsets.emplace_back();
        auto& infeasible = mInfeasibleSubsets.back();
        infeasible.emplace(inequality);

        const auto& begin = inequality.lhs().asUVariable();
        const auto& end = inequality.rhs().asUVariable();
        auto path = graph.get_path(begin, end).value();
        for (const auto& [u, v]: path) {
            infeasible.emplace(u, v, false);
        }
    }

    template<class Settings>
    void UnionFindModule<Settings>::propagate_induces_equalities(
                                    const std::unordered_set<carl::UVariable>& vars) noexcept
    {
        auto induced = [&] (auto const& lhs, auto const& rhs) -> bool {
            return (classes.has_variable(lhs) && classes.has_variable(rhs))
                && (classes.find(lhs) == classes.find(rhs));
        };

        for (const auto& ueq : informed) {
            const auto& lhs = ueq.lhs().asUVariable();
            const auto& rhs = ueq.rhs().asUVariable();

            if (vars.count(lhs) && vars.count(rhs) && induced(lhs, rhs)) {
                if (auto path = graph.get_path(lhs, rhs, Settings::lemma_length_bound)) {
                    FormulasT eqs;

                    for (const auto& [u, v]: path.value()) {
                        eqs.emplace_back(u, v, true);
                    }

                    eqs.emplace_back(ueq);

                    using carl::FormulaType;
                    addLemma(FormulaT{ FormulaType::OR, eqs });
                }
            }
        }
    }

    template<class Settings>
    Answer UnionFindModule<Settings>::checkCore()
    {
        if constexpr (Settings::use_theory_propagation) {
            propagate_induces_equalities(variables);
        }

        for (const auto& ueq : history) {
            if (ueq.negated()) {
                const auto& lhs = classes.find(ueq.lhs().asUVariable());
                const auto& rhs = classes.find(ueq.rhs().asUVariable());
                if (lhs == rhs) {
                    generateInfeasibleSubset(ueq);
                    return Answer::UNSAT;
                }
            }
        }

        return Answer::SAT;
    }
}

#include "Instantiation.h"
