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
 * @file Formula.h
 *
 * @author Ulrich Loup
 * @author Florian Corzilius
 * @since 2012-02-09
 * @version 2012-02-09
 */

#ifndef SMTRAT_FORMULA_H
#define SMTRAT_FORMULA_H

#include <vector>
#include <bitset>
#include <string.h>
#include <string>
#include "ModuleType.h"
#include "Constraint.h"

using namespace std;

namespace smtrat
{
    enum Type
    {
        AND, OR, NOT, IFF, XOR, IMPLIES, BOOL, REALCONSTRAINT, TTRUE, FFALSE
    };

    typedef std::bitset<64> Condition;

    static const Condition  PROP_TRUE = Condition();

    //Propositions which hold, if they hold for each subformula of a formula including itself (0-15)
    static const Condition PROP_IS_IN_NNF                       = Condition().set( 0, 1 );
    static const Condition PROP_IS_IN_CNF                       = Condition().set( 1, 1 ) | PROP_IS_IN_NNF;
    static const Condition PROP_IS_PURE_CONJUNCTION             = Condition().set( 2, 1 ) | PROP_IS_IN_CNF;
    static const Condition PROP_IS_A_CLAUSE                     = Condition().set( 3, 1 ) | PROP_IS_IN_CNF;
    static const Condition PROP_IS_A_LITERAL                    = Condition().set( 4, 1 ) | PROP_IS_A_CLAUSE | PROP_IS_PURE_CONJUNCTION;
    static const Condition PROP_IS_AN_ATOM                      = Condition().set( 5, 1 ) | PROP_IS_A_LITERAL;
    static const Condition PROP_VARIABLE_DEGREE_LESS_THAN_FIVE  = Condition().set( 6, 1 );
    static const Condition PROP_VARIABLE_DEGREE_LESS_THAN_FOUR  = Condition().set( 7, 1 ) | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
    static const Condition PROP_VARIABLE_DEGREE_LESS_THAN_THREE = Condition().set( 8, 1 ) | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR;
    static const Condition STRONG_CONDITIONS                    = PROP_IS_AN_ATOM | PROP_VARIABLE_DEGREE_LESS_THAN_THREE;

    //Propositions which hold, if they hold in at least one subformula (16-31)
    static const Condition PROP_CONTAINS_EQUATION                = Condition().set( 16, 1 );
    static const Condition PROP_CONTAINS_INEQUALITY              = Condition().set( 17, 1 );
    static const Condition PROP_CONTAINS_STRICT_INEQUALITY       = Condition().set( 18, 1 ) | PROP_CONTAINS_INEQUALITY;
    static const Condition PROP_CONTAINS_LINEAR_POLYNOMIAL       = Condition().set( 19, 1 );
    static const Condition PROP_CONTAINS_NONLINEAR_POLYNOMIAL    = Condition().set( 20, 1 );
    static const Condition PROP_CONTAINS_MULTIVARIATE_POLYNOMIAL = Condition().set( 21, 1 );
    static const Condition WEAK_CONDITIONS                       = PROP_CONTAINS_EQUATION | PROP_CONTAINS_INEQUALITY | PROP_CONTAINS_STRICT_INEQUALITY
                                             | PROP_CONTAINS_LINEAR_POLYNOMIAL | PROP_CONTAINS_LINEAR_POLYNOMIAL | PROP_CONTAINS_NONLINEAR_POLYNOMIAL
                                             | PROP_CONTAINS_MULTIVARIATE_POLYNOMIAL;

    //Propositions indicating that a solver cannot solve the formula
    static const Condition PROP_CANNOT_BE_SOLVED_BY_SIMPLIFIERMODULE    = Condition().set( 48, 1 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_GROEBNERMODULE      = Condition().set( 49, 1 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_VSMODULE            = Condition().set( 50, 1 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_UNIVARIATECADMODULE = Condition().set( 51, 1 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_CADMODULE           = Condition().set( 52, 1 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_SATMODULE           = Condition().set( 53, 1 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_LRAMODULE           = Condition().set( 54, 1 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_PREPROMODULE        = Condition().set( 55, 1 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_PREPROCNFMODULE     = Condition().set( 57, 1 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_CNFERMODULE         = Condition().set( 56, 1 );
    static const Condition SOLVABLE_CONDITIONS                          = PROP_CANNOT_BE_SOLVED_BY_SIMPLIFIERMODULE | PROP_CANNOT_BE_SOLVED_BY_GROEBNERMODULE
                                                 | PROP_CANNOT_BE_SOLVED_BY_VSMODULE | PROP_CANNOT_BE_SOLVED_BY_UNIVARIATECADMODULE
                                                 | PROP_CANNOT_BE_SOLVED_BY_CADMODULE | PROP_CANNOT_BE_SOLVED_BY_SATMODULE
                                                 | PROP_CANNOT_BE_SOLVED_BY_LRAMODULE | PROP_CANNOT_BE_SOLVED_BY_PREPROMODULE
                                                 | PROP_CANNOT_BE_SOLVED_BY_PREPROCNFMODULE | PROP_CANNOT_BE_SOLVED_BY_CNFERMODULE;

    class Formula
    {
        private:
            unsigned      mId;
            Type          mType;
            GiNaC::symtab mRealValuedVars;

            union
            {
                std::vector<Formula*>* mpSubformulas;
                const Constraint*      mpConstraint;
                const std::string*     mpIdentifier;
            };
            Formula*  mpFather;
            Condition mPropositions;
            bool      mPropositionsUptodate;

        public:
            Formula();
            Formula( const Type );
            Formula( const std::string& );
            Formula( const Constraint* _constraint );
            Formula( const Constraint& );
            Formula( const Formula& );
            ~Formula();

            /**
             * Type definitions.
             */
            typedef std::vector<Formula*>::const_iterator         const_iterator;
            typedef std::vector<Formula*>::const_reverse_iterator const_reverse_iterator;

            /**
             * Accessors:
             */
            unsigned id() const
            {
                return mId;
            }

            Type getType() const
            {
                return mType;
            }

            Condition proposition() const
            {
                assert( mPropositionsUptodate );
                return mPropositions;
            }

            unsigned numberOfVariables() const
            {
                return mRealValuedVars.size();
            }

            const GiNaC::symtab& realValuedVars() const
            {
                return mRealValuedVars;
            }

            GiNaC::symtab& rRealValuedVars()
            {
                return mRealValuedVars;
            }

            std::vector<Formula*>* const pSubformulas()
            {
                assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
                return mpSubformulas;
            }

            const std::vector<Formula*>& subformulas() const
            {
                assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
                return *mpSubformulas;
            }

            const Constraint* const pConstraint() const
            {
                assert( mType == REALCONSTRAINT );
                return mpConstraint;
            }

            const Constraint* pConstraint()
            {
                assert( mType == REALCONSTRAINT );
                return mpConstraint;
            }

            const Constraint& constraint() const
            {
                assert( mType == REALCONSTRAINT );
                return *mpConstraint;
            }

            const std::string& identifier() const
            {
                assert( mType == BOOL );
                return *mpIdentifier;
            }

            Formula* const pFather()
            {
                return mpFather;
            }

            const Formula* const cpFather() const
            {
                return mpFather;
            }

            const Formula& father() const
            {
                assert( mpFather != NULL );
                return *mpFather;
            }

            unsigned size() const
            {
                if( mType == BOOL || mType == REALCONSTRAINT || mType == TTRUE || mType == FFALSE )
                {
                    return 1;
                }
                else
                {
                    return mpSubformulas->size();
                }
            }

            bool empty() const
            {
                if( mType == BOOL || mType == REALCONSTRAINT || mType == TTRUE || mType == FFALSE )
                {
                    return false;
                }
                else
                {
                    return mpSubformulas->empty();
                }
            }

            // Important: Only the last subformula is allowed to be changed. This ensures the right assignment of the ID.
            const_iterator begin() const
            {
                assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
                return mpSubformulas->begin();
            }

            const_iterator end() const
            {
                assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
                return mpSubformulas->end();
            }

            // Important: Only the last subformula is allowed to be changed. This ensures the right assignment of the ID.
            const_reverse_iterator rbegin() const
            {
                assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
                return mpSubformulas->rbegin();
            }

            const_reverse_iterator rend() const
            {
                assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
                return mpSubformulas->rend();
            }

            // Important: Only the last subformula is allowed to be changed. This ensures the right assignment of the ID.
            const Formula* at( unsigned _pos ) const
            {
                assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
                assert( mpSubformulas->size() > _pos );
                return mpSubformulas->at( _pos );
            }

            const Formula& rAt( unsigned _pos ) const
            {
                assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
                assert( mpSubformulas->size() > _pos );
                return *mpSubformulas->at( _pos );
            }

            Formula* back()
            {
                assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
                assert( !mpSubformulas->empty() );
                return mpSubformulas->back();
            }

            const Formula* back() const
            {
                assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
                assert( !mpSubformulas->empty() );
                return mpSubformulas->back();
            }

            const Formula& rBack() const
            {
                assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
                assert( !mpSubformulas->empty() );
                return *mpSubformulas->back();
            }

            void resetFather()
            {
                mpFather = NULL;
            }

            Condition getPropositions();
            unsigned getMaxID() const;
            void updateID();
            void setFather( Formula* );
            void addSubformula( Formula* );
            void addSubformula( const Constraint* );
            void pop_back();
            void erase( unsigned );
            void erase( const Formula* );
            Formula* pruneBack();
            void clear();
            void notSolvableBy( ModuleType );
            void print( ostream& = std::cout, const string = "", bool = false ) const;
            void printPropositions( ostream& = std::cout, const string = "" ) const;
            void FormulaToConstraints( vector<const Constraint*>& ) const;

        private:

            void addConstraintPropositions( const Constraint& );
    };

}    // namespace smtrat

#endif // SMTRAT_FORMULA_H
