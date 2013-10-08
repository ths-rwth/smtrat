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
 * @version 2013-04-01
 */

#ifndef SMTRAT_FORMULA_H
#define SMTRAT_FORMULA_H

#include <string.h>
#include <string>
#include <set>
#include <unordered_map>
#include "Condition.h"
#include "modules/ModuleType.h"
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

            /// A flag indicating whether this formula is a deduction of the other sub-formulas of its father.
            bool mDeducted;
            /// A flag indicating whether the propositions of this formula are updated.
            bool mPropositionsUptodate;
            /// The set (initial) activity for this formula
            double mActivity;
            ///
            double mDifficulty;
            /// The type of this formula.
            Type mType;

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

        public:

            /// A pool to manage all generated constraints.
            static std::unique_ptr<ConstraintPool> mpConstraintPool;


            /**
             *  Constructors and destructor.
             */
            Formula();
            Formula( const Type );
            Formula( const std::string* );
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
             * Methods.
             */

            void setDeducted( bool _deducted )
            {
                mDeducted = _deducted;
            }

            bool deducted() const
            {
                return mDeducted;
            }

            const double& difficulty() const
            {
                return mDifficulty;
            }

            double difficulty()
            {
                return mDifficulty;
            }

            void setDifficulty( double difficulty )
            {
                mDifficulty = difficulty;
            }

            double activity() const
            {
                return mActivity;
            }

            void setActivity( double _activity )
            {
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
                mDifficulty = _formula->difficulty();

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
                        addSubformula( _formula->pruneFront() );
                    }
                }
                delete _formula;
            }

            Condition proposition() const
            {
                assert( mPropositionsUptodate );
                return mPropositions;
            }

            void realValuedVars( Variables& _realVars ) const
            {
                if( mType == REALCONSTRAINT )
                {
                    for( auto var = mpConstraint->variables().begin(); var != mpConstraint->variables().end(); ++var )
                        if( var->getType() == carl::VariableType::VT_REAL )
                            _realVars.insert( *var );
                }
                else if( isBooleanCombination() )
                {
                    for( auto subformula = mpSubformulas->begin(); subformula != mpSubformulas->end(); ++subformula )
                        (*subformula)->realValuedVars( _realVars );
                }
            }
            
            void integerValuedVars( Variables& _intVars ) const
            {
                if( mType == REALCONSTRAINT )
                {
                    for( auto var = mpConstraint->variables().begin(); var != mpConstraint->variables().end(); ++var )
                        if( var->getType() == carl::VariableType::VT_INT )
                            _intVars.insert( *var );
                }
                else if( isBooleanCombination() )
                {
                    for( auto subformula = mpSubformulas->begin(); subformula != mpSubformulas->end(); ++subformula )
                        (*subformula)->integerValuedVars( _intVars );
                }
            }
            
            void arithmeticVars( Variables& _arithmeticVars ) const
            {
                if( mType == REALCONSTRAINT )
                {
                    _arithmeticVars.insert( mpConstraint->variables().begin(), mpConstraint->variables().end() );
                }
                else if( isBooleanCombination() )
                {
                    for( auto subformula = mpSubformulas->begin(); subformula != mpSubformulas->end(); ++subformula )
                        (*subformula)->arithmeticVars( _arithmeticVars );
                }
            }

            void booleanVars( std::set< std::string >& _booleanVars ) const
            {
                if( mType == BOOL )
                {
                    _booleanVars.insert( *mpIdentifier );
                }
                else if( isBooleanCombination() )
                {
                    for( auto subformula = mpSubformulas->begin(); subformula != mpSubformulas->end(); ++subformula )
                        (*subformula)->booleanVars( _booleanVars );
                }
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
                assert( mType == REALCONSTRAINT || mType == TTRUE || mType == FFALSE );
                return mpConstraint;
            }

            const Constraint* pConstraint()
            {
                assert( mType == REALCONSTRAINT || mType == TTRUE || mType == FFALSE );
                return mpConstraint;
            }

            const Constraint& constraint() const
            {
                assert( mType == REALCONSTRAINT || mType == TTRUE || mType == FFALSE );
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

            static const Constraint* newBound( const carl::Variable& _var, const Constraint::Relation _rel, const Rational& _bound )
            {
                return mpConstraintPool->newBound( _var, _rel, _bound );
            }

            static const Constraint* newConstraint( const Polynomial& _lhs, const Constraint::Relation _rel )
            {
                return mpConstraintPool->newConstraint( _lhs, _rel );
            }

            static carl::Variable newRealVariable( const std::string& _name )
            {
                return mpConstraintPool->newArithmeticVariable( _name, carl::VariableType::VT_REAL );
            }

            static carl::Variable newArithmeticVariable( const std::string& _name, carl::VariableType _domain )
            {
                return mpConstraintPool->newArithmeticVariable( _name, _domain );
            }

            static void newBooleanVariable( const std::string& _name )
            {
                mpConstraintPool->newBooleanVariable( _name );
            }

            static const ConstraintPool& constraintPool()
            {
                return *mpConstraintPool;
            }

            /**
             * Generates a fresh real variable and returns its identifier.
             *
             * @return The fresh real variable.
             */
            static carl::Variable newAuxiliaryRealVariable()
            {
                return mpConstraintPool->newAuxiliaryRealVariable();
            }

            /**
             * Generates a fresh real variable and returns its identifier.
             * 
             * @param _varName
             * 
             * @return The fresh real variable.
             */
            static carl::Variable newAuxiliaryRealVariable( const std::string& _varName )
            {
                return mpConstraintPool->newAuxiliaryRealVariable( _varName );
            }
            
            /**
             * Generates a fresh Boolean variable and returns its identifier.
             *
             * @return The identifier of a fresh Boolean variable.
             */
            static std::string* newAuxiliaryBooleanVariable()
            {
                return mpConstraintPool->newAuxiliaryBooleanVariable();
            }

            bool isAtom() const
            {
                return (mType == REALCONSTRAINT || mType == BOOL || mType == FFALSE || mType == TTRUE);
            }

            bool isBooleanCombination() const
            {
                return (mType == AND || mType == OR || mType == NOT || mType == IMPLIES || mType == IFF || mType == XOR);
            }

            bool isConstraintConjunction() const
            {
                if( PROP_IS_PURE_CONJUNCTION <= proposition() )
                {
                    return !(PROP_CONTAINS_BOOLEAN <= proposition());
                }
                else
                {
                    return false;
                }
            }

            bool isRealConstraintConjunction() const
            {
                if( PROP_IS_PURE_CONJUNCTION <= proposition() )
                {
                    return (!(PROP_CONTAINS_INTEGER_VALUED_VARS <= proposition()) && !(PROP_CONTAINS_BOOLEAN <= proposition()));
                }
                else
                {
                    return false;
                }
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
            
            /**
             * Adds a constraint as sub-formula to this formula.
             * @param _constraint The constraint to add.
             */
            void addSubformula( const Constraint* _constraint )
            {
                addSubformula( new Formula( _constraint ) );
            }

            /**
             * Adds a Boolean variable as sub-formula to this formula.
             * @param _boolean The name of the Boolean variable to add.
             */
            void addSubformula( const std::string* _boolean )
            {
                addSubformula( new Formula( _boolean ) );
            }

            Condition getPropositions();
            void setFather( Formula* );
            void addSubformula( Formula* );
            iterator replace( iterator, Formula* );
            void pop_back();
            void pop_front();
            iterator erase( iterator );

            Formula* pruneBack();
            Formula* pruneFront();
            Formula* prune( unsigned );
            iterator prune( iterator );
            void clear();
            //void notSolvableBy( ModuleType );
            void print( std::ostream& = std::cout, const std::string = "", bool = false, bool = false ) const;
            void printProposition( std::ostream& _out = std::cout, const std::string _init = "" ) const;
            friend std::ostream& operator <<( std::ostream&, const Formula& );
            std::string toString( bool = false, bool = true ) const;
            void getConstraints( std::vector<const Constraint*>& ) const;
            static void toCNF( Formula&, bool = true );
            static bool resolveNegation( Formula&, bool = true );
            static std::string FormulaTypeToString( Type type);

            std::string variableListToString(std::string seperator = ",", const std::unordered_map<std::string, std::string>& variableIds = std::unordered_map<std::string, std::string>()) const;
            std::string toRedlogFormat(bool withVariables = true) const;

        private:

            void addConstraintPropositions( const Constraint& );
    };

    struct FormulaIteratorConstraintIdCompare
    {
        bool operator() ( Formula::const_iterator i1, Formula::const_iterator i2 ) const
        {
            return (*i1)->pConstraint()->id() < (*i2)->pConstraint()->id();
        }
    };
    
    
    struct FormulaConstraintCompare
    {
        bool operator( ) (const Formula::const_iterator& c1, const Formula::const_iterator & c2 ) const
        {
            return (( *c1 )->constraint( ) < ( *c2 )->constraint( ) );
        }
    };


}    // namespace smtrat

#endif // SMTRAT_FORMULA_H
