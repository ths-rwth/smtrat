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

#include <carl/formula/uninterpreted/UFInstanceManager.h>

namespace smtrat
{
    template<class Settings>
    UnionFindModule<Settings>::UnionFindModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
        Module( _formula, _conditionals, _manager )
        , classes(translate)
#ifdef SMTRAT_DEVOPTION_Statistics
        , mStatistics(Settings::moduleName)
#endif
    {
    }

    template<class Settings>
    UnionFindModule<Settings>::~UnionFindModule()
    {}

    template<class Settings>
    bool UnionFindModule<Settings>::informCore( const FormulaT& _constraint )
    {
        assert(_constraint.getType() == carl::UEQ);
        const auto& ueq = _constraint.uequality();
        assert(ueq.lhs().isUVariable() && ueq.rhs().isUVariable());

        const auto& lhs = ueq.lhs().asUVariable();
        const auto& rhs = ueq.rhs().asUVariable();

        if (ueq.negated()) {
            if (lhs == rhs)
                return false;
            if constexpr (Settings::use_theory_propagation) {
                informed.emplace(lhs, rhs, false);
            }
        } else {
            if constexpr (Settings::use_theory_propagation) {
                informed.emplace(ueq);
            }
        }
        return true;
    }

    template<class Settings>
    bool UnionFindModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        assert(_subformula->formula().getType() == carl::UEQ);
        const auto& ueq = _subformula->formula().uequality();
        assert(ueq.lhs().isUVariable() && ueq.rhs().isUVariable());

        const auto& lhs = ueq.lhs().asUVariable();
        const auto& rhs = ueq.rhs().asUVariable();

        // TODO process vars in inform core?
        auto process = [&] (const auto& var) {
            if (const auto& [it, inserted] = variables.emplace(var); inserted) {
                graph.add_vertex(var);
            }
            classes.introduce_variable(var);
        };

        process(lhs);
        process(rhs);

        if (!ueq.negated()) {
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
        assert(_subformula->formula().getType() == carl::UEQ);
        const auto& ueq = _subformula->formula().uequality();

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
                    classes.introduce_variable(a);
                    classes.introduce_variable(b);
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
        for (const auto& [u, v]: graph.get_path(begin, end)) {
            infeasible.emplace(u, v, false);
        }
    }

    template<class Settings>
    void UnionFindModule<Settings>::propagate_induces_equalities(const std::set<carl::UVariable>& vars) noexcept
    {
        auto induced = [&] (auto const& lhs, auto const& rhs) -> bool {
            return (classes.has_variable(lhs) && classes.has_variable(rhs))
                && (classes.find(lhs) == classes.find(rhs));
        };

        for (const auto& ueq : informed) {
            const auto& lhs = ueq.lhs().asUVariable();
            const auto& rhs = ueq.rhs().asUVariable();
            if (vars.count(lhs) && vars.count(rhs) && induced(lhs, rhs)) {
                FormulasT eqs;
                for (const auto& [u, v]: graph.get_path(lhs, rhs)) {
                    eqs.emplace_back(u, v, false);
                }

                using carl::FormulaType;
                FormulaT precondition( FormulaType::AND, eqs );
                addLemma(FormulaT{ FormulaType::IMPLIES, precondition, FormulaT{ueq} });
            }
        }
    }

    template<class Settings>
    Answer UnionFindModule<Settings>::checkCore()
    {
        if constexpr (Settings::use_theory_propagation) {
            // TODO benchmark help of filtering
            std::set<carl::UVariable> vars;
            for (const auto& ueq : history) {
                ueq.collectUVariables(vars);
            }

            propagate_induces_equalities(vars);
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
