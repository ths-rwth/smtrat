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

        history.emplace_back(ueq);
        variables.emplace(ueq.lhs().asUVariable());
        variables.emplace(ueq.rhs().asUVariable());

        return true;
    }

    template<class Settings>
    void UnionFindModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        assert(_subformula->formula().getType() == carl::UEQ);
        const auto& ueq = _subformula->formula().uequality();
        auto it = std::find(history.rbegin(), history.rend(), ueq);
        history.erase(std::next(it).base());
    }

    template<class Settings>
    void UnionFindModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == Answer::SAT )
        {
            // TODO
            // Your code.
        }
    }

    template<typename UF, typename Inequalities>
    [[nodiscard]] bool isConsistent(UF& union_find, const Inequalities& inequalities) noexcept {
        for (const auto &ueq : inequalities) {
            const auto& lhs = union_find.find(ueq.lhs().asUVariable());
            const auto& rhs = union_find.find(ueq.rhs().asUVariable());
            if (rhs == lhs)
                return false;
        }

        return true;
    }

    template<class Settings>
    Answer UnionFindModule<Settings>::checkCore()
    {
        UnionFind<carl::UVariable> union_find;
        union_find.init(variables);

        std::vector<carl::UEquality> inequalities;
        for (const auto &ueq : history) {
            assert(ueq.lhs().isUVariable() && ueq.rhs().isUVariable());
            if (ueq.negated()) {
                inequalities.emplace_back(ueq);
            } else {
                union_find.merge(ueq.lhs().asUVariable(), ueq.rhs().asUVariable());
            }
        }

        if (!isConsistent(union_find, inequalities)) {
            generateTrivialInfeasibleSubset();
            return Answer::UNSAT;
        } else {
            return Answer::SAT;
        }
    }
}

#include "Instantiation.h"
