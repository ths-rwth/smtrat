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
    void UnionFindModule<Settings>::check_restart() noexcept
    {
        if (reset) {
            classes.resize(variables);
            for (const auto& eq : history) {
                if (!eq.negated()) {
                    classes.merge(eq.lhs().asUVariable(), eq.rhs().asUVariable());
                }
            }
            reset = false;
        }
    }

    template<class Settings>
    bool UnionFindModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        assert(_subformula->formula().getType() == carl::UEQ);
        const auto& ueq = _subformula->formula().uequality();
        assert(ueq.lhs().isUVariable() && ueq.rhs().isUVariable());

        const auto& lhs = ueq.lhs().asUVariable();
        const auto& rhs = ueq.rhs().asUVariable();

        if (const auto& [it, inserted] = variables.emplace(lhs); inserted) {
            classes.introduce_variable(lhs);
        }

        if (const auto& [it, inserted] = variables.emplace(rhs); inserted) {
            classes.introduce_variable(rhs);
        }

        if (!ueq.negated()) {
            check_restart();
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
        history.erase(std::next(it).base());
        reset = true;
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

    template<typename Classes, typename Inequalities>
    [[nodiscard]] bool isConsistent(Classes& classes, const Inequalities& inequalities) noexcept {
        for (const auto &ueq : inequalities) {
            const auto& lhs = classes.find(ueq.lhs().asUVariable());
            const auto& rhs = classes.find(ueq.rhs().asUVariable());
            if (rhs == lhs)
                return false;
        }

        return true;
    }

    template<class Settings>
    Answer UnionFindModule<Settings>::checkCore()
    {
        std::vector<carl::UEquality> inequalities;
        std::copy_if(history.begin(), history.end(), std::back_inserter(inequalities), [] (const auto &ueq) {
            return ueq.negated();
        });

        check_restart();

        if (!isConsistent(classes, inequalities)) {
            generateTrivialInfeasibleSubset();
            return Answer::UNSAT;
        } else {
            return Answer::SAT;
        }
    }
}

#include "Instantiation.h"
