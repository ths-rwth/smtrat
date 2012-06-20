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
#include <string.h>
#include <string>
#include "Condition.h"
#include "ModuleType.h"
#include "ConstraintPool.h"

namespace smtrat
{
    enum Type
    {
        AND, OR, NOT, IFF, XOR, IMPLIES, BOOL, REALCONSTRAINT, TTRUE, FFALSE
    };

    class Formula
    {
        private:
            /**
             *  Members.
             */

            /// A unique ID within the formula containing this formula.
            unsigned      mId;
            /// The type of this formula.
            Type          mType;
            /// All real valued variables used within this formula (and its subformulas).
            GiNaC::symtab mRealValuedVars;
            /// The content of this formula.
            union
            {
                std::vector<Formula*>* mpSubformulas;
                const Constraint*      mpConstraint;
                const std::string*     mpIdentifier;
            };
            /// The formula which contains this formula as subformula.
            Formula* mpFather;
            /// The propositions of this formula.
            Condition mPropositions;
            /// A flag indicating whether the propositions of this formula are updated.
            bool mPropositionsUptodate;

        public:

            /// A pool to manage all generated constraints.
            static ConstraintPool mConstraintPool;
            /// The prefix for any auxiliary Boolean defined in this formula.
            static const std::string mAuxiliaryBooleanNamePrefix;
            /// A counter for the auxiliary Booleans defined in this formula.
            static unsigned mAuxiliaryBooleanCounter;
            /// The prefix for any auxiliary Boolean defined in this formula.
            static const std::string mAuxiliaryRealNamePrefix;
            /// A counter for the auxiliary Booleans defined in this formula.
            static unsigned mAuxiliaryRealCounter;

            /**
             *  Constructors and destructor.
             */
            Formula();
            Formula( const Type );
            Formula( const std::string& );
            Formula( const Constraint* _constraint );
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
                assert( isBooleanCombination() );
                return mpSubformulas;
            }

            const std::vector<Formula*>& subformulas() const
            {
                assert( isBooleanCombination() );
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
                assert( isBooleanCombination() );
                return mpSubformulas->begin();
            }

            const_iterator end() const
            {
                assert( isBooleanCombination() );
                return mpSubformulas->end();
            }

            // Important: Only the last subformula is allowed to be changed. This ensures the right assignment of the ID.
            const_reverse_iterator rbegin() const
            {
                assert( isBooleanCombination() );
                return mpSubformulas->rbegin();
            }

            const_reverse_iterator rend() const
            {
                assert( isBooleanCombination() );
                return mpSubformulas->rend();
            }

            // Important: Only the last subformula is allowed to be changed. This ensures the right assignment of the ID.
            const Formula* at( unsigned _pos ) const
            {
                assert( isBooleanCombination() );
                assert( mpSubformulas->size() > _pos );
                return mpSubformulas->at( _pos );
            }

            const Formula& rAt( unsigned _pos ) const
            {
                assert( isBooleanCombination() );
                assert( mpSubformulas->size() > _pos );
                return *mpSubformulas->at( _pos );
            }

            Formula* back()
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                return mpSubformulas->back();
            }

            const Formula* back() const
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                return mpSubformulas->back();
            }

            const Formula& rBack() const
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                return *mpSubformulas->back();
            }

            void resetFather()
            {
                mpFather = NULL;
            }

            static const Constraint* newConstraint( const GiNaC::ex& _lhs, const Constraint_Relation _rel )
            {
                return mConstraintPool.newConstraint( _lhs, _rel );
            }

            static const Constraint* newConstraint( const std::string& _stringrep, const bool _infix = true, const bool _polarity = true )
            {
                return mConstraintPool.newConstraint( _stringrep, _infix, _polarity );
            }

            static GiNaC::ex newVariable( const std::string& _name )
            {
                return mConstraintPool.newVariable( _name );
            }

            /**
             * Generates a fresh real variable and returns its identifier.
             *
             * @return The identifier of a fresh real variable.
             */
            static std::string getAuxiliaryReal()
            {
                std::stringstream out;
                out << mAuxiliaryRealNamePrefix << mAuxiliaryRealCounter++;
                return out.str();
            }

            /**
             * Generates a fresh Boolean variable and returns its identifier.
             *
             * @return The identifier of a fresh Boolean variable.
             */
            static std::string getAuxiliaryBoolean()
            {
                std::stringstream out;
                out << mAuxiliaryBooleanNamePrefix << mAuxiliaryBooleanCounter++;
                return out.str();
            }

            bool isAtom() const
            {
                return ( mType == REALCONSTRAINT || mType == BOOL || mType == FFALSE || mType == TTRUE );
            }

            bool isBooleanCombination() const
            {
                return ( mType == AND || mType == OR || mType == NOT || mType == IMPLIES || mType == IFF || mType == XOR );
            }

            bool contains( const Formula* const _formula ) const
            {
                if( isBooleanCombination() )
                {
                    return (std::find( mpSubformulas->begin(), mpSubformulas->end(), _formula ) != mpSubformulas->end());
                }
                return false;
            }

            bool contains( const std::vector< const Formula* >& _formulas ) const
            {
                std::set< const Formula* > subformulas = std::set< const Formula* >();
                for( std::vector< const Formula* >::const_iterator subformula = _formulas.begin();
                     subformula != _formulas.end(); ++subformula )
                {
                    subformulas.insert( *subformula );
                }
                return contains( subformulas );
            }

            bool contains( const std::set< const Formula* >& _formulas ) const
            {
                std::set< const Formula* > subformulas = std::set< const Formula* >();
                for( const_iterator subformula = begin(); subformula != end(); ++subformula )
                {
                    subformulas.insert( *subformula );
                }
                std::set< const Formula* >::iterator subformula = subformulas.begin();
                std::set< const Formula* >::iterator iter = _formulas.begin();
                while( subformula != subformulas.end() && iter != _formulas.end() )
                {
                    subformula = subformulas.insert( subformula, *iter );
                    ++iter;
                }
                return (iter == _formulas.end());
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
            Formula* prune( unsigned );
            void clear();
            void notSolvableBy( ModuleType );
            void print( std::ostream& = std::cout, const std::string = "", bool = false ) const;
            void printPropositions( std::ostream& = std::cout, const std::string = "" ) const;
            void FormulaToConstraints( std::vector<const Constraint*>& ) const;

        private:

            void addConstraintPropositions( const Constraint& );
    };

}    // namespace smtrat

#endif // SMTRAT_FORMULA_H
