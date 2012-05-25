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

/* 
 * File:   PreProCNFModule.h
 * Author: Dennis Scully
 *
 * Created on 15. May 2012, 14:14
 */

#ifndef SMTRAT_PreProCNFModule_H
#define SMTRAT_PreProCNFModule_H

#include "../Module.h"
#include <ginac/ginac.h>
#include <ginac/flags.h>
#include <vector>

namespace smtrat
{
    class PreProCNFModule:
        public Module
    {
        public:
            
            /**
             * Constructors:
             */
            PreProCNFModule( Manager* const _tsManager, const Formula* const _formula );
           
            /**
             * Destructor:
             */
            virtual ~PreProCNFModule();
            
            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubFormula( const Formula* const );
            Answer isConsistent();
            void substituteConstraints( const Formula& );
            void popBacktrackPoint();
            void pushBacktrackPoint();

        private:
            
            std::vector< unsigned >          mActivities;
            std::vector< Formula* >          mFormula;
            std::vector<const Formula*>      mConstraintOrigins;
            std::vector< Formula* >          mBacktrackPoint;
            bool                             mNewFormulaReceived;
            unsigned                         mNumberOfSubstitutedFormulas;
            unsigned                         mNumberOfAppliedSubstitutions;
            std::vector< pair< pair<std::string, bool>, pair<GiNaC::ex, GiNaC::ex> > > mSubstitutions;
            std::vector< const Formula* >    mSubstitutionOrigins;
    };

}    // namespace smtrat
#endif   /** PreProCNFModule_H */
