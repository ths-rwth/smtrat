/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * @file   PreprocessingModule.h
 *         Created on January 10, 2013, 9:59 PM
 * @author: Sebastian Junges
 *
 * 
 */

#pragma once

#include "../../Module.h"

#include "../../VariableConstraintGraph.h"

namespace smtrat
{
    class VRWModule : public Module
    {
        protected:
            VariableConstraintGraph mMatchingGraph;
            /// mapping received constraint -> node in the graph
            std::map<Formula::const_iterator, std::list<ConstraintNode*>::iterator, dereference_compare> mConstraintPositions; 
            
        public:
            /**
             * Constructors:
             */
            VRWModule( ModuleType, const Formula* const,  RuntimeSettings*, Manager* const _tsManager );

            /**
             * Destructor:
             */
            virtual ~VRWModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );
            
            void printConstraintPositions();
    };

}    // namespace smtrat

