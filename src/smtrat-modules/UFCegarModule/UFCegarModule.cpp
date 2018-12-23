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

    std::string flatten_name(const carl::UTerm& term);

    std::string flatten_name_impl(const carl::UVariable& var) {
        return var.variable().name();
    }

    std::string flatten_name_impl(const carl::UFInstance& ufi) {
        const auto& fn = ufi.uninterpretedFunction();

        auto concat = [&] (std::string res, const carl::UTerm& term) {
            return std::move(res) + '.' + flatten_name(term);
        };

        const auto &args = ufi.args();
        auto suffix = std::accumulate(args.begin(), args.end(), std::string(""), concat);

        return '(' + fn.name() + suffix + ')';
    }


    std::string flatten_name(const carl::UTerm& term) {
        return std::visit( [&] (const auto& var) -> std::string {
            return flatten_name_impl(var);
        }, term.asVariant());
    }

    template<class Settings>
    auto UFCegarModule<Settings>::flatten(const UTerm& term) noexcept -> UTerm
    {
        if (auto res = term_store.find(term); res != term_store.end()) {
            return res->second;
        }

        auto name = flatten_name(term);

        if (term.isUFInstance()) {
            const auto& ufi = term.asUFInstance();
            instances[ufi.uninterpretedFunction()].emplace(ufi);
        }

        UTerm flattened{ UVariable(freshUninterpretedVariable(name), my_sort) };
        term_store.emplace(term, flattened);
        return flattened;
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
    bool UFCegarModule<Settings>::refine(const UFInstance& a, const UFInstance& b) noexcept
    {
        using carl::FormulaType;

        if (refined.count(a) && refined.count(b))
            return false;

        auto args = std::make_pair(a.args().begin(), b.args().begin());
        auto end = a.args().end();

        auto term = [&] (const auto& val) { return term_store[val]; };

        FormulasT conditions;
        for ( ; args.first != end; ++args.first, ++args.second ) {
            conditions.emplace_back(term(*args.first), term(*args.second), false);
        }

        auto consequence = carl::UEquality(term(a), term(b), false);

        FormulaT constraint{ FormulaType::IMPLIES, // TODO is this only validity ???
            FormulaT( FormulaType::AND, conditions ),
            FormulaT( consequence )
        };

        addSubformulaToPassedFormula(constraint);

        refined.emplace(a);
        refined.emplace(b);
        return true;
    }

    template<class Settings>
    bool UFCegarModule<Settings>::refine() noexcept {
        /*using Class = carl::SortValue;
        std::unordered_map<Class, std::vector<carl::UVariable>> classes;
        for (const auto& var : backendsModel() ) {
            classes[var.second.asSortValue()].push_back(var.first.asUVariable());
        }*/

        bool added_constraint = false;

        // generate functional consistency
        for (const auto& [function, list] : instances) {
            if (list.size() <= 1)
                continue;

            for (auto i = list.begin(); i != std::prev(list.end()); ++i) {
                for (auto j = std::next(list.begin()); j != list.end(); ++j) {
                    added_constraint |= refine(*i, *j);
                }
            }
        }

        return added_constraint;
    }

    template<class Settings>
    Answer UFCegarModule<Settings>::checkCore()
    {
        Answer result = runBackends();
        bool refinable = true;

        while (result == Answer::SAT && refinable) {
            refinable = refine();
            result = runBackends();
        }

        if (result == Answer::SAT) {
            getBackendsModel();
        } else if (result == Answer::UNSAT) {
            getInfeasibleSubsets();
        }

        return result;
    }
}

#include "Instantiation.h"
