/**
 * @file UnionFindModule.h
 * @author Henrich Lauko <xlauko@mail.muni.cz>
 * @author Dominika Krejci <dominika.krejci@rwth-aachen.de>
 *
 * @version 2018-11-18
 * Created on 2018-11-18.
 */

#pragma once

#include <smtrat-modules/Module.h>
#include "UnionFindStatistics.h"
#include "UnionFindSettings.h"
#include "UnionFind.h"
#include "EQGraph.h"

namespace smtrat
{
    using Type = carl::UVariable;

    template<typename Impl>
    using EQClasses = UnionFindInterface< Type, Impl >;

    using StaticClasses = EQClasses< StaticUnionFind >;
    using BacktrackableClasses = EQClasses< Backtrackable< PersistentUnionFind > >;

    /* slasses setup */
    using Classes = BacktrackableClasses;

    template<typename Settings>
    class UnionFindModule : public Module
    {
        private:
#ifdef SMTRAT_DEVOPTION_Statistics
            UnionFindStatistics mStatistics;
#endif
        using History = std::vector<carl::UEquality>;
        History history;

        EQGraph<carl::UVariable> graph;

        void generateInfeasibleSubset(const carl::UEquality& inequality);

        void propagate_induces_equalities(const std::set<carl::UVariable>& vars) noexcept;

        mutable Classes classes;

        using TranslateMap = typename Classes::TranslateMap;
        TranslateMap translate;

        bool need_to_update = false;
        std::unordered_set<carl::UVariable> variables;

        std::unordered_set<carl::UEquality> informed;
        public:
            typedef Settings SettingsType;
            std::string moduleName() const {
                return SettingsType::moduleName;
            }
            UnionFindModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

            ~UnionFindModule();

            // Main interfaces.
            /**
             * Informs the module about the given constraint. It should be tried to inform this
             * module about any constraint it could receive eventually before assertSubformula
             * is called (preferably for the first time, but at least before adding a formula
             * containing that constraint).
             * @param _constraint The constraint to inform about.
             * @return false, if it can be easily decided whether the given constraint is inconsistent;
             *        true, otherwise.
             */
            bool informCore( const FormulaT& _constraint );

            /**
             * The module has to take the given sub-formula of the received formula into account.
             *
             * @param _subformula The sub-formula to take additionally into account.
             * @return false, if it can be easily decided that this sub-formula causes a conflict with
             *        the already considered sub-formulas;
             *        true, otherwise.
             */
            bool addCore( ModuleInput::const_iterator _subformula );

            /**
             * Removes the subformula of the received formula at the given position to the considered ones of this module.
             * Note that this includes every stored calculation which depended on this subformula, but should keep the other
             * stored calculation, if possible, untouched.
             *
             * @param _subformula The position of the subformula to remove.
             */
            void removeCore( ModuleInput::const_iterator _subformula );

            /**
             * Updates the current assignment into the model.
             * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
             */
            void updateModel() const;

            /**
             * Checks the received formula for consistency.
             * @return True,    if the received formula is satisfiable;
             *       False,   if the received formula is not satisfiable;
             *       Unknown, otherwise.
             */
            Answer checkCore();
    };
}
