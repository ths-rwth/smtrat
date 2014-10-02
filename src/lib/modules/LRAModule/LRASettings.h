/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
/**
 * Class to create a settings object for the LRAModule.
 * @file LRASettings.h
 * @author Florian Corzilius
 * @since 2014-10-01
 * @version 2014-10-01
 */

#pragma once

#include "../../datastructures/lra/TableauSettings.h"
    
namespace smtrat
{
    struct LRASettings1
    {
        /**
         * 
         */
        static const bool simple_theory_propagation = true;
        /**
         * 
         */
        static const bool simple_conflict_search = true;
        /**
         * 
         */
        static const bool simple_conflicts_and_propagation_on_demand = true;
        /**
         * 
         */
        static const bool one_conflict_reason = false;
        /**
         * 
         */
        static const bool restore_previous_consistent_assignment = false;
        /**
         * 
         */
        static const bool branch_and_bound_early = false;
        /**
         * 
         */
        static const bool use_gomory_cuts = false;
        /**
         * 
         */
        static const bool use_cuts_from_proofs = false;
        /**
         * 
         */
        struct Tableau_settings : lra::TableauSettings1 {};
    };
}

