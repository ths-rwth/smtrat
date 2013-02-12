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
#include "PreprocessingSettings.h"

#define ADDLINEARDEDUCTIONS
//#define PREPROCESSING_DEVELOP_MODE

namespace smtrat
{

    const int squaresArray[30]  = { 0*0 , 1*1, 2*2, 3*3, 4*4, 5*5, 6*6, 7*7, 8*8, 9*9,
                                    10*10, 11*11, 12*12, 13*13, 14*14, 15*15, 16*16, 17*17, 18*18, 19*19,
                                    20*20, 21*21, 22*22, 23*23, 24*24, 25*25, 26*26, 27*27, 28*28, 29*29 };
    const std::vector<int> squares( squaresArray, squaresArray+30 );

    /**
     *
     */
    class PreprocessingModule : public Module
    {
        protected:

        public:

            PreprocessingModule( ModuleType, const Formula* const,  RuntimeSettings*, Manager* const _tsManager );

            /**
             * Destructor:
             */
            virtual ~PreprocessingModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );

        protected:
            void setDifficulty( Formula* formula, bool invert = false );
            Formula* splitProductConstraints( Formula* );
            void rewritePotentialInequalities( Formula* formula, bool invert = false );
            void assignActivitiesToPassedFormula();
            void addLinearDeductions( Formula* formula );
            void addUpperBounds( Formula* formula, const GiNaC::symtab& symbols, GiNaC::numeric boundary, bool strict ) const;
            GiNaC::numeric determineUpperBounds( unsigned degree, const GiNaC::numeric& constPart ) const;
    };

}    // namespace smtrat

