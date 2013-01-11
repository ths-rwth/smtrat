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
 * @author Sebastian Junges
 * @since 2012-02-09
 * @version 2012-10-12
 */

#ifndef SMTRAT_FORMULA_H
#define SMTRAT_FORMULA_H

#include <string.h>
#include <string>
#include <set>
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
            double mActivity;
            /// The type of this formula.
            Type mType;
            /// All real valued variables used within this formula (and its sub formulas).
            GiNaC::symtab mRealValuedVars;
            /// All Boolean variables used within this formula (and its sub formulas).
            std::set< std::string, strCmp > mBooleanVars;

            /// The content of this formula.
            union
            {
                std::list<Formula*>* mpSubformulas;
                const Constraint*    mpConstraint;
                const std::string*   mpIdentifier;
            };
            /// The formula which contains this formula as sub formula.
            Formula* mpFather;
            /// The propositions of this formula.
            Condition mPropositions;
            /// A flag indicating whether the propositions of this formula are updated.
            bool mPropositionsUptodate;

        public:

            /// A pool to manage all generated constraints.
            static ConstraintPool mConstraintPool;
            ///
            static double mSumOfAllActivities;
            ///
            static unsigned mNumberOfNonZeroActivities;

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
            typedef std::list<Formula*>::iterator               iterator;
            typedef std::list<Formula*>::reverse_iterator       reverse_iterator;
            typedef std::list<Formula*>::const_iterator         const_iterator;
            typedef std::list<Formula*>::const_reverse_iterator const_reverse_iterator;

            /**
             * Accessors:
             */

            double activity() const
            {
                return mActivity;
            }

            void setActivity( double _activity )
            {
                if( mActivity == 0 )
                {
                    ++Formula::mNumberOfNonZeroActivities;
                    Formula::mSumOfAllActivities += _activity;
                }
                mActivity = _activity;
            }

            Type getType() const
            {
                return mType;
            }

            void copyAndDelete( Formula* _formula )
            {
                assert( _formula != this );
                mType = _formula->getType();
                if( _formula->getType() == BOOL )
                {
                    if( isBooleanCombination() )
                    {
                        delete mpSubformulas;
                    }
                    mpIdentifier = new std::string( _formula->identifier() );
                }
                else if( _formula->getType() == REALCONSTRAINT )
                {
                    if( isBooleanCombination() )
                    {
                        delete mpSubformulas;
                    }
                    else if( mType == BOOL )
                    {
                        delete mpIdentifier;
                    }
                    mpConstraint = _formula->pConstraint();
                }
                else if( _formula->getType() == TTRUE || _formula->getType() == FFALSE )
                {
                    if( isBooleanCombination() )
                    {
                        delete mpSubformulas;
                    }
                    else if( mType == BOOL )
                    {
                        delete mpIdentifier;
                    }
                    mpSubformulas = NULL;
                }
                else
                {
                    if( mType == BOOL )
                    {
                        delete mpIdentifier;
                    }
                    if( !isBooleanCombination() )
                    {
                        mpSubformulas = new std::list<Formula*>();
                    }
                    while( !_formula->empty() )
                    {
                        addSubformula( _formula->pruneBack() );
                    }
                }
                delete _formula;
            }

            Condition proposition() const
            {
                assert( mPropositionsUptodate );
                return mPropositions;
            }

            unsigned numberOfRealVariables() const
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

            unsigned numberOfBooleanVariables() const
            {
                return mBooleanVars.size();
            }

            const std::set< std::string, strCmp >& booleanVars() const
            {
                return mBooleanVars;
            }

            std::list<Formula*>* const pSubformulas()
            {
                assert( isBooleanCombination() );
                return mpSubformulas;
            }

            const std::list<Formula*>& subformulas() const
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

            iterator begin()
            {
                assert( isBooleanCombination() );
                return mpSubformulas->begin();
            }

            iterator end()
            {
                assert( isBooleanCombination() );
                return mpSubformulas->end();
            }

            const_iterator end() const
            {
                assert( isBooleanCombination() );
                return mpSubformulas->end();
            }

            // Important: Only the last sub formula is allowed to be changed. This ensures the right assignment of the ID.
            const_reverse_iterator rbegin() const
            {
                assert( isBooleanCombination() );
                return mpSubformulas->rbegin();
            }

            reverse_iterator rbegin()
            {
                assert( isBooleanCombination() );
                return mpSubformulas->rbegin();
            }

            reverse_iterator rend()
            {
                assert( isBooleanCombination() );
                return mpSubformulas->rend();
            }

            const_reverse_iterator rend() const
            {
                assert( isBooleanCombination() );
                return mpSubformulas->rend();
            }

            iterator last()
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                iterator result = --mpSubformulas->end();
                return result;
            }

            const_iterator last() const
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                const_iterator result = --mpSubformulas->end();
                return result;
            }

            // Important: Only the last subformula is allowed to be changed. This ensures the right assignment of the ID.
            const Formula* at( unsigned _pos ) const
            {
                assert( isBooleanCombination() );
                assert( mpSubformulas->size() > _pos );
                unsigned                posNr = 0;
                Formula::const_iterator pos   = begin();
                while( posNr < _pos )
                {
                    ++pos;
                    ++posNr;
                }
                return *pos;

            }

            const Formula& rAt( unsigned _pos ) const
            {
                assert( isBooleanCombination() );
                assert( mpSubformulas->size() > _pos );
                unsigned                posNr = 0;
                Formula::const_iterator pos   = begin();
                while( posNr < _pos )
                {
                    ++pos;
                    ++posNr;
                }
                return **pos;

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

            static const Constraint* newConstraint( const GiNaC::ex& _lhs, const Constraint_Relation _rel, const GiNaC::symtab& _variables, bool _variablesOverApproximated = true )
            {
                return mConstraintPool.newConstraint( _lhs, _rel, _variables, _variablesOverApproximated );
            }

            static const Constraint* newConstraint( const std::string& _stringrep, const bool _infix = true, const bool _polarity = true )
            {
                return mConstraintPool.newConstraint( _stringrep, _infix, _polarity );
            }

            static const Constraint* newConstraint( const std::string& _lhsRep, const std::string& _rhsRep, Constraint_Relation _rel, const std::set< std::string >& _variables )
            {
                return mConstraintPool.newConstraint( _lhsRep, _rhsRep, _rel, _variables );
            }

            static GiNaC::ex newVariable( const std::string& _name )
            {
                return mConstraintPool.newVariable( _name );
            }

            static const ConstraintPool& constraintPool()
            {
                return mConstraintPool;
            }

            /**
             * Generates a fresh real variable and returns its identifier.
             *
             * @return The fresh real variable.
             */
            static std::pair<std::string,GiNaC::ex> newAuxiliaryReal()
            {
                return mConstraintPool.newAuxiliaryReal();
            }

            /**
             * Generates a fresh Boolean variable and returns its identifier.
             *
             * @return The identifier of a fresh Boolean variable.
             */
            static std::string newAuxiliaryBoolean()
            {
                return mConstraintPool.newAuxiliaryBoolean();
            }

            bool isAtom() const
            {
                return (mType == REALCONSTRAINT || mType == BOOL || mType == FFALSE || mType == TTRUE);
            }

            bool isBooleanCombination() const
            {
                return (mType == AND || mType == OR || mType == NOT || mType == IMPLIES || mType == IFF || mType == XOR);
            }

            bool contains( const Formula* const _formula ) const
            {
                if( isBooleanCombination() )
                {
                    return (std::find( mpSubformulas->begin(), mpSubformulas->end(), _formula ) != mpSubformulas->end());
                }
                return false;
            }

            bool contains( const std::vector<const Formula*>& _formulas ) const
            {
                std::set<const Formula*> subformulas = std::set<const Formula*>();
                for( std::vector<const Formula*>::const_iterator subformula = _formulas.begin(); subformula != _formulas.end(); ++subformula )
                {
                    subformulas.insert( *subformula );
                }
                return contains( subformulas );
            }

            bool contains( const std::set<const Formula*>& _formulas ) const
            {
                std::set<const Formula*> subformulas = std::set<const Formula*>();
                for( const_iterator subformula = begin(); subformula != end(); ++subformula )
                {
                    subformulas.insert( *subformula );
                }
                std::set<const Formula*>::iterator subformula = subformulas.begin();
                std::set<const Formula*>::iterator iter       = _formulas.begin();
                while( subformula != subformulas.end() && iter != _formulas.end() )
                {
                    subformula = subformulas.insert( subformula, *iter );
                    ++iter;
                }
                return (iter == _formulas.end());
            }

            Condition getPropositions();
            void setFather( Formula* );
            void addSubformula( Formula* );
            void addSubformula( const Constraint* );
            void pop_back();
            void erase( unsigned );
            void erase( const Formula* );
            iterator erase( iterator );

            Formula* pruneBack();
            Formula* prune( unsigned );
            iterator prune( iterator );
            void clear();
            void notSolvableBy( ModuleType );
            void print( std::ostream& = std::cout, const std::string = "", bool = false, bool = false ) const;
            friend std::ostream& operator <<( std::ostream&, const Formula& );
            std::string toString( bool = false ) const;
            void getConstraints( std::vector<const Constraint*>& ) const;
            static void toCNF( Formula&, bool = true );
            static bool resolveNegation( Formula&, bool = true );
            static std::string FormulaTypeToString( Type type);

            std::string variableListToString(std::string seperator) const;
            std::string toRedlogFormat(bool withVariables = true) const;

        private:

            void addConstraintPropositions( const Constraint& );
    };

}    // namespace smtrat

#endif // SMTRAT_FORMULA_H
