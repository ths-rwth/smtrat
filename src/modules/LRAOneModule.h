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
 * @file LRAOneModule.h
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#ifndef LRAONEMODULE_H
#define LRAONEMODULE_H

#include "../Module.h"
#include "LRAOneModule/Value.h"
#include "LRAOneModule/Variable.h"
#include "LRAOneModule/Bound.h"
#include <stdio.h>

namespace smtrat
{
    class LRAOneModule:
        public Module
    {
        public:
            struct exPointerComp
            {
                bool operator ()( const GiNaC::ex* const pExA, const GiNaC::ex* const pExB ) const
                {
                    return GiNaC::ex_is_less()( *pExA, *pExB );
                }
            };
            typedef std::map<const GiNaC::ex*, lraone::Variable*, exPointerComp>            ExVariableMap;
            typedef std::pair<const Constraint* const , std::vector<const lraone::Bound*> > ConstraintBoundPair;
            typedef std::map<const Constraint* const , std::vector<const lraone::Bound*> >  ConstraintBoundMap;
            typedef std::map<const Constraint*, const Formula* const >                      ConstraintFormulaMap;
            typedef std::map<const lraone::Bound* const , const Constraint*>                BoundConstraintMap;
            typedef std::pair<unsigned, unsigned>                                           Position;
            typedef std::map<Position, GiNaC::numeric>                                      Tableau;

        private:

            /**
             * Members:
             */
            Tableau                        mTableau;
            std::vector<lraone::Variable*> mAllVars;    // vector which saves the order of the priorities
            std::vector<const Constraint*> mAllConstraints;
            bool                           mInitialized;
            unsigned                       mRowMaximum;
            unsigned                       mColumnMaximum;
            lraone::Variable*              mPivotNonBasicVar;
            GiNaC::numeric                 mPivotCoeff;
            ExVariableMap                  mExistingVars;
            BoundConstraintMap             mBoundToConstraint;
            ConstraintFormulaMap           mConstraintToFormula;
            ConstraintBoundMap             mConstraintToBound;

        public:

            /**
             * Constructors:
             */
            LRAOneModule( Manager* const _tsManager, const Formula* const _formula );

            /**
             * Destructor:
             */
            virtual ~LRAOneModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            bool inform( const Constraint* const );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );

            void pivotingStep();

            void printAssignments( std::ostream& = std::cout ) const;
            void printVariables( std::ostream& = std::cout ) const;
            void printTableau( std::ostream& = std::cout ) const;

        private:

            /**
             * Methods:
             */
            void activateBound( lraone::Variable&, const lraone::Bound* );
            void setBound( lraone::Variable&, const Constraint_Relation&, bool, GiNaC::numeric&, const Constraint* );
            void initialize();
            void initPriority();
            bool isInConflict( unsigned, bool );
            void getConflicts( unsigned, bool );
            void pivotAndUpdate( lraone::Variable*, lraone::Variable*, const lraone::Bound&, GiNaC::numeric& );
            lraone::Variable* getVar( bool, unsigned );
    };

}    // namespace smtrat

#endif   /* LRAONEMODULE_H */
