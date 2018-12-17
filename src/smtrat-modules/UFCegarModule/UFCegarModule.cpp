/**
 * @file UFCegarModule.cpp
 * @author Henrich Lauko <xlauko@mail.muni.cz>
 * @author Dominika Krejci <dominika.krejci@rwth-aachen.de>
 *
 * @version 2018-11-18
 * Created on 2018-11-18.
 */

#include "UFCegarModule.h"

#include <carl/formula/uninterpreted/UFInstanceManager.h>

namespace smtrat
{
    using carl::freshUninterpretedVariable;
    using carl::overloaded;
    using carl::SortManager;

    template<class Settings>
    UFCegarModule<Settings>::UFCegarModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
        Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
        , mStatistics(Settings::moduleName)
#endif
    {
        const std::string sort_name = "__my_cegar_sort";
        my_sort = SortManager::getInstance().addSort( sort_name );
    }

    template<class Settings>
    UFCegarModule<Settings>::~UFCegarModule()
    {}

    template<class Settings>
    bool UFCegarModule<Settings>::informCore( const FormulaT& /*_constraint*/ )
    {
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void UFCegarModule<Settings>::init()
    {
    }

    template<class Settings>
    auto UFCegarModule<Settings>::flatten(const FormulaT& formula) noexcept -> FormulaT
    {
        if (auto res = formula_store.find(formula); res != formula_store.end()) {
            return res->second;
        }

        const auto& ueq = formula.uequality();
        FormulaT eq{flatten(ueq.lhs()), flatten(ueq.rhs()), ueq.negated()};
        formula_store.emplace(formula, eq);
        return eq;
    }

    template<class Settings>
    auto UFCegarModule<Settings>::flatten(const UTerm& term) noexcept -> UTerm
    {
        if (auto res = term_store.find(term); res != term_store.end()) {
            return res->second;
        }

        auto uvar = [&] (const std::string& name) -> UVariable {
            return UVariable(freshUninterpretedVariable(name), my_sort);
        };

        auto res = std::visit(overloaded {
            [&](const UVariable& var) {
                return UTerm{uvar(var.variable().name())};
            },
            [&](const UFInstance& ufi) {
                const auto& fn = ufi.uninterpretedFunction();
                return UTerm{uvar(fn.name())};
            }
        }, term.asVariant());

        term_store.emplace(term, res);
        return res;
    }

    template<class Settings>
    bool UFCegarModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        carl::FormulaVisitor<FormulaT> visitor;

        auto flattened = visitor.visitResult( _subformula->formula(), [&] (const auto& formula) {
            if (formula.getType() == carl::UEQ)
                return flatten(formula);
            else
                return formula;
        } );

        addSubformulaToPassedFormula(flattened, _subformula->formula());
        return true;
    }

    template<class Settings>
    void UFCegarModule<Settings>::removeCore( ModuleInput::const_iterator /*_subformula*/ )
    {
    }

    template<class Settings>
    void UFCegarModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == Answer::SAT )
        {
            // Your code.
        }
    }

    template<class Settings>
    Answer UFCegarModule<Settings>::checkCore()
    {
        auto result = runBackends();
        if (result == Answer::SAT) {
            getBackendsModel();
        }

        if (result == Answer::UNSAT) {
            getInfeasibleSubsets();
        }

        return result;
    }
}

#include "Instantiation.h"
