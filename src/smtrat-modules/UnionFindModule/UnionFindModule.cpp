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

#include <boost/graph/adjacency_list.hpp>
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
    bool UnionFindModule<Settings>::informCore( const FormulaT& /*_constraint*/ )
    {
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void UnionFindModule<Settings>::init()
    {
    }

    template<class Settings>
    bool UnionFindModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        assert(_subformula->formula().getType() == carl::UEQ);
        const auto& ueq = _subformula->formula().uequality();
        assert(ueq.lhs().isUVariable() && ueq.rhs().isUVariable());

        const auto& lhs = ueq.lhs().asUVariable();
        const auto& rhs = ueq.rhs().asUVariable();

        auto process = [&] (const auto& var) {
            variables.emplace(var);
            classes.introduce_variable(var);
        };

        process(lhs);
        process(rhs);

        if (!ueq.negated()) {
            classes.merge(lhs, rhs);
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

            // reinsert history tail
            if (it != history.rbegin()) {
                History tail;
                for (auto eq = it.base(); eq != history.end(); ++eq) {
                    if (!eq->negated()) {
                        const auto& a = eq->lhs().asUVariable();
                        const auto& b = eq->rhs().asUVariable();
                        classes.introduce_variable(a);
                        classes.introduce_variable(b);
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

                mModel.emplace(var.variable(), sorts[cls]);
            }
        }
    }

    template<class Settings>
    Answer UnionFindModule<Settings>::checkCore()
    {
        for (const auto& ueq : history) {
            if (ueq.negated()) {
                const auto& lhs = classes.find(ueq.lhs().asUVariable());
                const auto& rhs = classes.find(ueq.rhs().asUVariable());
                if (lhs == rhs) {
                    generateTrivialInfeasibleSubset();
                    return Answer::UNSAT;
                }
            }
        }

        return Answer::SAT;
    }
}

#include "Instantiation.h"
