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
 * File:   PreProModule.h
 * Author: Dennis Scully
 *
 * Created on 23. April 2012, 14:53
 */

#ifndef SMTRAT_PreProModule_H
#define SMTRAT_PreProModule_H

#include "../Module.h"

namespace smtrat
{
    class PreProModule:
        public Module
    {
        public:

            /**
             * Constructors:
             */
            PreProModule( Manager* const _tsManager, const Formula* const _formula );

            /**
             * Destructor:
             */
            virtual ~PreProModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubFormula( const Formula* const );
            Answer isConsistent();
            void addLearningClauses();
            void proceedSubstitution();
            void simplifyConstraints();
            std::pair< const Formula*, const Formula* > isCandidateforSubstitution( const Formula* const ) const;
            bool substituteConstraint( const Formula* const, std::pair< std::pair< std::string, bool >,
                    std::pair< std::pair<GiNaC::symtab, GiNaC::symtab>, std::pair< GiNaC::ex, GiNaC::ex> > >,
                    vec_set_const_pFormula );
            void popBacktrackPoint();
            void pushBacktrackPoint();

        private:
            
            // Members for AddLearningClauses()
            bool                        mFreshConstraintReceived;
            std::vector<const Constraint*>   mReceivedConstraints;
            std::vector<const Formula*>      mConstraintOrigins;
            std::vector< std::pair< std::pair< bool, unsigned >, std::pair< unsigned, unsigned > > >  mConstraintBacktrackPoints;
            
            // Members for proceedSubstitution()
            bool                        mNewFormulaReceived;
            unsigned                    mNumberOfComparedConstraints;
            unsigned                    mNumberOfCheckedFormulas;
            std::vector< vec_set_const_pFormula >                               mSubstitutionOrigins;
            std::map< std::string, unsigned >                                   mNumberOfVariables;
            std::vector< std::pair< std::pair< std::string, bool >, std::pair< std::pair<GiNaC::symtab, GiNaC::symtab>, std::pair< GiNaC::ex, GiNaC::ex> > > >    mSubstitutions;
            
    };

}    // namespace smtrat
#endif   /** PreProModule_H */