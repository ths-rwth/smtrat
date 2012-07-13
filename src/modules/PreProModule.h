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
            bool assertSubformula( Formula::const_iterator );
            bool inform( const Constraint* const );
            Answer isConsistent();
            void addLearningClauses();
            void proceedSubstitution();
            void simplifyClauses();
            void assignActivities();
            void generateVarActivitiesInDatabase( Formula* );
            void generateConActivitiesInDatabase( Formula* );
            void generateFinalActivitiesInDatabase( Formula* );
            void assignActivitiesFromDatabase( Formula* );
            
            std::pair< const Formula*, const Formula* > isCandidateforSubstitution( Formula::const_iterator ) const;
            Formula::iterator substituteConstraint( Formula::iterator, std::pair< std::pair< std::string, bool >,
                    std::pair< std::pair<GiNaC::symtab, GiNaC::symtab>, std::pair< GiNaC::ex, GiNaC::ex> > >,
                    vec_set_const_pFormula );
            void removeSubformula( Formula::const_iterator );
            const Constraint_Relation getInvertedRelationSymbol( const Constraint* const );
            void getConstraints( Formula*, std::vector<const Constraint*>&, bool);
            Formula::iterator interfaceRemoveSubformulaFromPassedFormula( Formula::iterator );
            Formula* removeConstraint(Formula*, GiNaC::ex, Constraint_Relation);
    

        private:

            // Members for AddLearningClauses()
            std::vector<const Constraint*>                                      mConstraints;
            std::vector< std::set<const Formula*> >                             mConstraintOrigins;
            std::vector<std::pair<std::pair<bool, unsigned>, 
            std::pair<unsigned, unsigned> > >                                   mConstraintBacktrackPoints;

            // Members for proceedSubstitution()
            bool                                                                mNewFormulaReceived;
            unsigned                                                            mNumberOfComparedConstraints;
            std::list<Formula*>::iterator                                       mLastCheckedFormula;
            std::vector< vec_set_const_pFormula >                               mSubstitutionOrigins;
            std::map< std::string, unsigned >                                   mNumberOfVariables;
            std::vector< std::pair< std::pair< std::string, bool >, 
            std::pair< std::pair<GiNaC::symtab, GiNaC::symtab>, 
            std::pair< GiNaC::ex, GiNaC::ex> > > >                              mSubstitutions;
            
            // Members for assignActivities()
            std::map< std::string, 
            std::pair<double, double> >                                         mVariableActivities;
            std::map< const Constraint*, 
            std::pair< std::pair<double, double>, std::pair<double, double> > > mConstraintActivities;
            double                                                              mMaxRelWeight;
            double                                                              mMaxVarDegreeActivity;
            double                                                              mMaxConDegreeActivity;
            double                                                              mMaxVarQuantityActivity;
            double                                                              mMaxConQuantityActivity;
            std::map< const Constraint*, double >                               mActivities;
            double                                                              mMinActivity;
            double                                                              mMaxActivity;
    };

}    // namespace smtrat
#endif   /** PreProModule_H */
