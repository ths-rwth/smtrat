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
 * @file ModuleInput.h
 * @author Florian Corzilius
 * @version 2014-05-16
 */

#ifndef SMTRAT_MODULE_INPUT_H
#define SMTRAT_MODULE_INPUT_H


#include <algorithm>
#include <list>
#include "../ConstraintPool.h"
#include "../FormulaPool.h"
#include "../config.h"

namespace smtrat
{   
    ///
    class ModuleInput : public std::list<const Formula*>
    {
        // Member.
        /// Store some properties about the conjunction of the stored formulas.
        mutable Condition mProperties;
        
        public:
            
        ModuleInput(): 
            std::list<const Formula*>(),
            mProperties()
        {}
        
        // Methods.
        
        const Condition& properties() const
        {
            updateProperties();
            return mProperties;
        }
        
        /**
         * @return true, if this formula is a conjunction of constraints;
         *          false, otherwise.
         */
        bool isConstraintConjunction() const
        {
            if( PROP_IS_PURE_CONJUNCTION <= mProperties )
                return !(PROP_CONTAINS_BOOLEAN <= mProperties);
            else
                return false;
        }

        /**
         * @return true, if this formula is a conjunction of real constraints;
         *          false, otherwise.
         */
        bool isRealConstraintConjunction() const
        {
            if( PROP_IS_PURE_CONJUNCTION <= mProperties )
                return (!(PROP_CONTAINS_INTEGER_VALUED_VARS <= mProperties) && !(PROP_CONTAINS_BOOLEAN <= mProperties));
            else
                return false;
        }

        /**
         * @return true, if this formula is a conjunction of integer constraints;
         *         false, otherwise.
         */
        bool isIntegerConstraintConjunction() const
        {
            if( PROP_IS_PURE_CONJUNCTION <= mProperties )
                return (!(PROP_CONTAINS_REAL_VALUED_VARS <= mProperties) && !(PROP_CONTAINS_BOOLEAN <= mProperties));
            else
                return false;
        }
        
        /**
         * @param _assignment The model to check conjunction of the stored formulas against.
         * @return 1, if the conjunction of the stored formulas is satisfied by the given model;
         *         0, if the given model conflicts the conjunction of the stored formulas;
         *         2, if it cannot be determined cheaply, whether the given model conflicts or satisfies 
         *            the conjunction of the stored formulas.
         */
        unsigned satisfiedBy( const Model& _assignment ) const
        {
            EvalRationalMap rationalAssigns;
            if( getRationalAssignmentsFromModel( _assignment, rationalAssigns ) )
                return satisfiedBy( rationalAssigns );
            else
                return 2; // TODO: Check also models having square roots as value.
        }
        
        /**
         * @param _assignment The assignment to check conjunction of the stored formulas against.
         * @return 1, if the conjunction of the stored formulas is satisfied by the given assignment;
         *         0, if the given assignment conflicts the conjunction of the stored formulas;
         *         2, if it cannot be determined cheaply, whether the given assignment conflicts or satisfies 
         *            the conjunction of the stored formulas.
         */
        unsigned satisfiedBy( const EvalRationalMap& _assignment ) const;
        
        /**
         * @param _subformula The formula for which to check whether it is one of the stored formulas.
         * @return true, if the given formula is one of the stored formulas;
         *         false, otherwise.
         */
        bool contains( const Formula* _subformula ) const
        {
            return std::find( begin(), end(), _subformula ) != end();
        }
        
        void updateProperties() const;
        
        /**
         * Collects all real valued variables occurring in this formula.
         * @param _realVars The container to collect the real valued variables in.
         */
        void realValuedVars( Variables& _realVars ) const
        {
            for( const Formula* subformula : *this )
                subformula->realValuedVars( _realVars );
        }

        /**
         * Collects all integer valued variables occurring in this formula.
         * @param _intVars The container to collect the integer valued variables in.
         */
        void integerValuedVars( Variables& _intVars ) const
        {
            for( const Formula* subformula : *this )
                subformula->integerValuedVars( _intVars );
        }

        /**
         * Collects all arithmetic variables occurring in this formula.
         * @param _arithmeticVars The container to collect the arithmetic variables in.
         */
        void arithmeticVars( Variables& _arithmeticVars ) const
        {
            for( const Formula* subformula : *this )
                subformula->arithmeticVars( _arithmeticVars );
        }

        /**
         * Collects all Boolean variables occurring in this formula.
         * @param _booleanVars The container to collect the Boolean variables in.
         */
        void booleanVars( Variables& _booleanVars ) const
        {
            for( const Formula* subformula : *this )
                subformula->booleanVars( _booleanVars );
        }
        
        struct IteratorCompare
        {
            bool operator() ( const_iterator i1, const_iterator i2 ) const
            {
                return (**i1) < (**i2);
            }
        };
        
        std::string toString() const
        {
            std::string result = "(and";
            for( const Formula* form : *this )
                result += " " + form->toString();
            result += ")";
            return result;
        }
        
//        friend std::ostream& operator<<( std::ostream& _out, const ModuleInput& _mi )
//        {
//            return _out << _mi.toString()
//        }
    };
}    // namespace smtrat
#endif   /* SMTRAT_MODULE_INPUT_H */
