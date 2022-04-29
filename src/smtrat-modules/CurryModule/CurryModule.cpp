/**
 * @file CurryModule.cpp
 * @author Henrich Lauko <xlauko@mail.muni.cz>
 * @author Dominika Krejci <dominika.krejci@rwth-aachen.de>
 *
 * @version 2018-11-18
 * Created on 2018-11-18.
 */

#include "CurryModule.h"

#include <carl-formula/uninterpreted/UFInstanceManager.h>

namespace smtrat
{
    using carl::overloaded;
    using carl::freshUninterpretedVariable;
    using carl::newUninterpretedFunction;
    using carl::newUFInstance;
    using carl::SortManager;

    template<class Settings>
    CurryModule<Settings>::CurryModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
        Module( _formula, _conditionals, _manager )
    {
        const std::string sort_name = "__curry_sort";
        curry_sort = SortManager::getInstance().addSort( sort_name );
        curry_function = newUninterpretedFunction( "__curry", {curry_sort, curry_sort}, curry_sort );
    }

    template<class Settings>
    CurryModule<Settings>::~CurryModule()
    {}

    template<class Settings>
    bool CurryModule<Settings>::informCore( const FormulaT& /*_constraint*/ )
    {
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void CurryModule<Settings>::init()
    {
    }

    template<class Settings>
    auto CurryModule<Settings>::curry(const FormulaT& formula) noexcept -> FormulaT
    {
        assert(formula.getType() == carl::UEQ);

        if (auto res = formula_store.find(formula); res != formula_store.end()) {
            return res->second;
        }

        const auto& ueq = formula.uequality();

        auto eq = FormulaT(curry(ueq.lhs()), curry(ueq.rhs()), ueq.negated());
        formula_store.emplace(formula, eq);
        return eq;
    }

    template<class Settings>
    auto CurryModule<Settings>::curry(const UTerm& term) noexcept -> UTerm
    {
        if (auto res = term_store.find(term); res != term_store.end()) {
            return res->second;
        }

        auto uvar = [&] (const std::string& name) -> UVariable {
            return UVariable( freshUninterpretedVariable(name), curry_sort );
        };

        auto res = std::visit(overloaded {
            [&](const UVariable& var) {
                return UTerm{uvar(var.variable().name())};
            },
            [&](const UFInstance& ufi) {
                UTerm sub;
                const auto& fn = ufi.uninterpretedFunction();
                if ( auto c = constants_store.find(fn); c != constants_store.end()) {
                    sub = c->second;
                } else {
                    sub = UTerm{uvar(fn.name())};
                    constants_store.emplace(fn, sub);
                }

                for (const auto& arg : ufi.args()) {
                    sub = newUFInstance(curry_function, {sub, curry(arg)});
                }
                return sub;
            }
        }, term.asVariant());

        term_store.emplace(term, res);
        return res;
    }

    template<class Settings>
    auto CurryModule<Settings>::flatten(const UTerm& term, std::vector<FormulaT>& flat) noexcept -> UVariable
    {
        if ( term.isUVariable() ) {
            return term.asUVariable();
        } else {
            if (auto res = flattened_terms.find(term); res != flattened_terms.end()) {
                auto& vec = flat_substitution[res->second];
                std::copy(vec.begin(), vec.end(), std::back_inserter(flat));
                return res->second;
            }

            auto ufi = term.asUFInstance();

            assert( ufi.args().size() == 2 );
            std::vector<FormulaT> substitution;
            auto lhs = flatten(ufi.args()[0], substitution);
            auto rhs = flatten(ufi.args()[1], substitution);

            auto fn = newUFInstance(curry_function, {lhs, rhs});
            auto new_var = UVariable( freshUninterpretedVariable(), curry_sort );
            substitution.emplace_back(fn, new_var, false);

            std::copy(substitution.begin(), substitution.end(), std::back_inserter(flat));

            flattened_terms.emplace(term, new_var);
            flat_substitution[new_var] = std::move(substitution);
            return new_var;
        }
    }

    template<class Settings>
    auto CurryModule<Settings>::flatten(const FormulaT& formula) noexcept -> const std::vector<FormulaT>&
    {
        assert(formula.getType() == carl::UEQ);
        if (auto res = flattened_store.find(formula); res != flattened_store.end()) {
            return res->second;
        }

        const auto& ueq = formula.uequality();

        std::vector<FormulaT> substitution;
        auto lhs = flatten(ueq.lhs(), substitution);
        auto rhs = flatten(ueq.rhs(), substitution);
        substitution.emplace_back(lhs, rhs, ueq.negated());

        flattened_store[formula] = std::move(substitution);
        return flattened_store[formula];
    }

    template<class Settings>
    bool CurryModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        carl::FormulaVisitor<FormulaT> visitor;

        auto curryfied = visitor.visitResult( _subformula->formula(), [&] (const auto& formula) {
            if (formula.getType() == carl::UEQ)
                return curry(formula);
            else
                return formula;
        } );

        auto flattened = visitor.visitResult( curryfied, [&] (const auto& formula) {
            if (formula.getType() == carl::UEQ)
                return FormulaT(carl::FormulaType::AND, flatten(formula));
            else
                return formula;
        } );

        addSubformulaToPassedFormula(flattened, _subformula->formula());
        return true;
    }

    template<class Settings>
    void CurryModule<Settings>::removeCore( ModuleInput::const_iterator /*_subformula*/ )
    {
    }

    template<class Settings>
    void CurryModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == Answer::SAT )
        {
            // Your code.
        }
    }

    template<class Settings>
    Answer CurryModule<Settings>::checkCore()
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
