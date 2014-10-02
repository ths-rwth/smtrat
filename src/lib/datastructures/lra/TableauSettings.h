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
 * Class to create a settings object for the Tableau.
 * @file TableauSettings.h
 * @author Florian Corzilius
 * @since 2014-10-01
 * @version 2014-10-01
 */

#pragma once

namespace smtrat
{   
    namespace lra
    {
        struct TableauSettings1
        {
            /**
             * 
             */
            static const bool use_pivoting_strategy = true;
            /**
             * 
             */
            static const bool use_refinement = true;
            /**
             * 
             */
            static const bool prefer_equations = false;
            /**
             * 
             */
            static const bool pivot_into_local_conflict = true;
            /**
             * 
             */
            static const bool use_activity_based_pivot_strategy = false;
            /**
             * 
             */
            static const bool use_theta_based_pivot_strategy = false;
            /**
             * 
             */
            static const bool introduce_new_constraint_in_refinement = false;
        };
    }
}
