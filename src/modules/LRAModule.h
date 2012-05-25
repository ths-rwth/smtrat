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
 * @file LRAModule.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2012-02-10
 * Created on January 18, 2012, 3:51 PM
 */

#ifndef SMTRAT_LRAMODULE_H
#define SMTRAT_LRAMODULE_H

#include "../Module.h"
#include "LRAModule/LRASolverA.h"

namespace smtrat
{
    class LRAModule:
        public Module
    {
    	private:
    		typedef std::pair< const Constraint*, bool > cons_bool_pair;
    		typedef std::vector< cons_bool_pair > cons_bool_pair_vec;
    		typedef std::map< const Constraint* const, cons_bool_pair_vec > cons_to_cons_bool_pair_vec_map;
        public:

            /**
             * Constructors:
             */
            LRAModule( Manager* const _tsManager, const Formula* const );

            /**
             * Destructor:
             */
            virtual ~LRAModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubFormula( const Formula* const );
            bool inform( const Constraint* const );
            Answer isConsistent();
            void popBacktrackPoint();
            void pushBacktrackPoint();

        private:
			lra::LRASolverA* 				mpLRASolver;
			cons_to_cons_bool_pair_vec_map 	mLRASolverConstraints;
			unsigned 						mNumAddedNonlinearConstraints;
            /**
             * Methods:
             */
			cons_to_cons_bool_pair_vec_map::const_iterator addConstraintToLRASolverConstraints( const Constraint* const );
    };

}    // namespace smtrat

#endif   /* LRAMODULE_H */
