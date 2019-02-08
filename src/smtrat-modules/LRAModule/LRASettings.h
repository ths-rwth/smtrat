/**
 * Class to create a settings object for the LRAModule.
 * @file LRASettings.h
 * @author Florian Corzilius
 * @since 2014-10-01
 * @version 2014-10-01
 */

#pragma once

#include "tableau/TableauSettings.h"

namespace smtrat
{
    struct LRASettings1
    {
		static constexpr auto moduleName = "LRAModule<LRASettings1>";
        /**
         *
         */
        static const bool simple_theory_propagation = true;
        /**
         *
         */
        static const bool learn_refinements = true;
        /**
         *
         */
        static const bool one_conflict_reason = false;
        /**
         *
         */
        static const bool use_gomory_cuts = true;
        /**
         *
         */
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        typedef Rational BoundType;
        #else
        typedef carl::Numeric<Rational> BoundType;
        #endif
        /**
         *
         */
        #ifdef SMTRAT_STRAT_PARALLEL_MODE
        typedef Rational EntryType;
        #else
        typedef carl::Numeric<Rational> EntryType;
        #endif
        /**
         *
         */
        struct Tableau_settings : lra::TableauSettings1 {};
    };

    struct LRASettings2 : LRASettings1
    {
		static constexpr auto moduleName = "LRAModule<LRASettings2>";
        typedef Rational BoundType;
        typedef Rational EntryType;
        static const bool simple_theory_propagation = false;
        static const bool learn_refinements = false;
        static const bool one_conflict_reason = true;
        struct Tableau_settings : lra::TableauSettings3 {};
    };
    
    struct LRASettingsICP : LRASettings1
    {
		static constexpr auto moduleName = "LRAModule<LRASettingsICP>";
        static const bool simple_theory_propagation = false;
        static const bool learn_refinements = false;
        static const bool one_conflict_reason = true;
        struct Tableau_settings : lra::TableauSettings3 {};
    };
}
