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
    enum Type { AND, OR, NOT, IFF, XOR, IMPLIES, BOOL, CONSTRAINT, TTRUE, FFALSE };

    class Formula
    {
        public:
            typedef std::list<Formula*>::iterator               iterator;
            typedef std::list<Formula*>::reverse_iterator       reverse_iterator;
            typedef std::list<Formula*>::const_iterator         const_iterator;
            typedef std::list<Formula*>::const_reverse_iterator const_reverse_iterator;
            
        private:

            // Members.

            // The deduction flag, which indicates, that this formula g is a direct sub-formula of
            // a conjunction of formulas (and g f_1 .. f_n), and, that (implies (and f_1 .. f_n) g) holds.
            bool mDeducted;
            // A flag indicating whether the propositions of this formula are updated.
            bool mPropositionsUptodate;
            // The activity for this formula, which means, how much is this formula involved in the solving procedure.
            double mActivity;
            // Some value stating an expected difficulty of solving this formula for satisfiability.
            double mDifficulty;
            // The type of this formula.
            Type mType;
            // The content of this formula.
            union
            {
                std::list<Formula*>* mpSubformulas;
                const Constraint*    mpConstraint;
                const std::string*   mpIdentifier;
            };
            // The formula which contains this formula as sub formula.
            Formula* mpFather;
            // The propositions of this formula.
            Condition mPropositions;

        public:

            // A pool to manage all generated constraints.
            static std::unique_ptr<ConstraintPool> mpConstraintPool;

            /**
             * [Default constructor] Constructs the formula (true).
             */
            Formula();
            
            /**
             * Constructs the formula of the given type. It is either one of the atoms (true) and (false)
             * or it is a formula (boolean_op arglist), where arglist is still empty. The arguments can/have
             * to be added belatedly with, e.g., addSubformula( .. ).
             * @param _type The type of the formula to construct.
             */
            Formula( const Type _type );
            
            /**
             * Constructs a formula being a Boolean variable.
             * @param _booleanVarName The pointer to the string representing the name of the Boolean variable.
             */
            Formula( const std::string* _booleanVarName );
            
            /**
             * Constructs a formula being a constraint.
             * @param _constraint The pointer to the constraint.
             */
            Formula( const Constraint* _constraint );
            
            /**
             * [Copy constructor] Constructs a copy the given formula. Note that all sub-formulas are also
             * copied and not only the pointers to them. Hence, this is a rather expensive operation.
             * @param _formula The formula to copy.
             */
            Formula( const Formula& _formula );

            /**
             * Destructor.
             */
            ~Formula();

            // Methods.

            /**
             * Sets the deduction flag to the given value..
             * @param _deducted The value to set the deduction flag to.
             */
            void setDeducted( bool _deducted )
            {
                mDeducted = _deducted;
            }

            /**
             * @return The deduction flag, which indicates, that this formula g is a direct sub-formula of
             *          a conjunction of formulas (and g f_1 .. f_n), and, that (implies (and f_1 .. f_n) g) holds.
             */
            bool deducted() const
            {
                return mDeducted;
            }

            /**
             * @return Some value stating an expected difficulty of solving this formula for satisfiability.
             */
            const double& difficulty() const
            {
                return mDifficulty;
            }

            /**
             * Sets the difficulty to the given value.
             * @param difficulty The value to set the difficulty to.
             */
            void setDifficulty( double difficulty )
            {
                mDifficulty = difficulty;
            }

            /**
             * @return The activity for this formula, which means, how much is this formula involved in the solving procedure.
             */
            double activity() const
            {
                return mActivity;
            }

            /**
             * Sets the activity to the given value.
             * @param _activity The value to set the activity to.
             */
            void setActivity( double _activity )
            {
                mActivity = _activity;
            }

            /**
             * @return The type of this formula.
             */
            Type getType() const
            {
                return mType;
            }

            /**
             * @return The bit-vector representing the propositions of this formula. For further
             *          information see the Condition class.
             */
            Condition proposition() const
            {
                assert( mPropositionsUptodate );
                return mPropositions;
            }

            /**
             * Collects all real valued variables occurring in this formula.
             * @param _realVars The container to collect the real valued variables in.
             */
            void realValuedVars( Variables& _realVars ) const
            {
                if( mType == CONSTRAINT )
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
            
            /**
             * Collects all integer valued variables occurring in this formula.
             * @param _intVars The container to collect the integer valued variables in.
             */
            void integerValuedVars( Variables& _intVars ) const
            {
                if( mType == CONSTRAINT )
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
            
            /**
             * Collects all arithmetic variables occurring in this formula.
             * @param _arithmeticVars The container to collect the arithmetic variables in.
             */
            void arithmeticVars( Variables& _arithmeticVars ) const
            {
                if( mType == CONSTRAINT )
                    _arithmeticVars.insert( mpConstraint->variables().begin(), mpConstraint->variables().end() );
                else if( isBooleanCombination() )
                {
                    for( auto subformula = mpSubformulas->begin(); subformula != mpSubformulas->end(); ++subformula )
                        (*subformula)->arithmeticVars( _arithmeticVars );
                }
            }

            /**
             * Collects all Boolean variables occurring in this formula.
             * @param _booleanVars The container to collect the Boolean variables in.
             */
            void booleanVars( std::set< std::string >& _booleanVars ) const
            {
                if( mType == BOOL )
                    _booleanVars.insert( *mpIdentifier );
                else if( isBooleanCombination() )
                {
                    for( auto subformula = mpSubformulas->begin(); subformula != mpSubformulas->end(); ++subformula )
                        (*subformula)->booleanVars( _booleanVars );
                }
            }

            /**
             * @return A pointer to the list of sub-formulas of this formula. Note, that
             *          this formula has to be a Boolean combination, if you invoke this method.
             */
            std::list<Formula*>* const pSubformulas()
            {
                assert( isBooleanCombination() );
                return mpSubformulas;
            }

            /**
             * @return A constant reference to the list of sub-formulas of this formula. Note, that
             *          this formula has to be a Boolean combination, if you invoke this method.
             */
            const std::list<Formula*>& subformulas() const
            {
                assert( isBooleanCombination() );
                return *mpSubformulas;
            }

            /**
             * @return A pointer to the constraint represented by this formula. Note, that
             *          this formula has to be of type CONSTRAINT, if you invoke this method.
             */
            const Constraint* const pConstraint() const
            {
                assert( mType == CONSTRAINT || mType == TTRUE || mType == FFALSE );
                return mpConstraint;
            }

            /**
             * @return A pointer to the constraint represented by this formula. Note, that
             *          this formula has to be of type CONSTRAINT, if you invoke this method.
             */
            const Constraint* pConstraint()
            {
                assert( mType == CONSTRAINT || mType == TTRUE || mType == FFALSE );
                return mpConstraint;
            }

            /**
             * @return A constant reference to the constraint represented by this formula. Note, that
             *          this formula has to be of type CONSTRAINT, if you invoke this method.
             */
            const Constraint& constraint() const
            {
                assert( mType == CONSTRAINT || mType == TTRUE || mType == FFALSE );
                return *mpConstraint;
            }

            /**
             * @return The name of the Boolean variable represented by this formula. Note, that
             *          this formula has to be of type BOOL, if you invoke this method.
             */
            const std::string& identifier() const
            {
                assert( mType == BOOL );
                return *mpIdentifier;
            }

            /**
             * @return A pointer to the father of this formula. Note, that this formula has 
             *          to have a father if you invoke this method.
             */
            Formula* const pFather()
            {
                return mpFather;
            }

            /**
             * @return A pointer to the father of this formula. Note, that this formula has 
             *          to have a father if you invoke this method.
             */
            const Formula* const cpFather() const
            {
                return mpFather;
            }

            /**
             * @return A constant reference to the father of this formula. Note, that this formula has 
             *          to have a father if you invoke this method.
             */
            const Formula& father() const
            {
                assert( mpFather != NULL );
                return *mpFather;
            }

            /**
             * @return The number of sub-formulas of this formula.
             */
            unsigned size() const
            {
                if( mType == BOOL || mType == CONSTRAINT || mType == TTRUE || mType == FFALSE )
                    return 1;
                else
                    return mpSubformulas->size();
            }

            /**
             * @return true, if this formula has sub-formulas;
             *          false, otherwise.
             */
            bool empty() const
            {
                if( mType == BOOL || mType == CONSTRAINT || mType == TTRUE || mType == FFALSE )
                    return false;
                else
                    return mpSubformulas->empty();
            }

            /**
             * @return An iterator to the beginning of the list of sub-formulas of this formula.
             */
            iterator begin()
            {
                assert( isBooleanCombination() );
                return mpSubformulas->begin();
            }

            /**
             * @return An iterator to the end of the list of sub-formulas of this formula.
             */
            iterator end()
            {
                assert( isBooleanCombination() );
                return mpSubformulas->end();
            }

            /**
             * @return A constant iterator to the beginning of the list of sub-formulas of this formula.
             */
            const_iterator begin() const
            {
                assert( isBooleanCombination() );
                return mpSubformulas->begin();
            }

            /**
             * @return A constant iterator to the end of the list of sub-formulas of this formula.
             */
            const_iterator end() const
            {
                assert( isBooleanCombination() );
                return mpSubformulas->end();
            }

            /**
             * @return An reverse iterator to the beginning of the list of sub-formulas of this formula.
             */
            reverse_iterator rbegin()
            {
                assert( isBooleanCombination() );
                return mpSubformulas->rbegin();
            }

            /**
             * @return An reverse iterator to the end of the list of sub-formulas of this formula.
             */
            reverse_iterator rend()
            {
                assert( isBooleanCombination() );
                return mpSubformulas->rend();
            }

            /**
             * @return A constant reverse iterator to the beginning of the list of sub-formulas of this formula.
             */
            const_reverse_iterator rbegin() const
            {
                assert( isBooleanCombination() );
                return mpSubformulas->rbegin();
            }

            /**
             * @return A constant reverse iterator to the end of the list of sub-formulas of this formula.
             */
            const_reverse_iterator rend() const
            {
                assert( isBooleanCombination() );
                return mpSubformulas->rend();
            }

            /**
             * @return An iterator to the last element. Note, that it presumes that there is at least one sub-formula.
             */
            iterator last()
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                iterator result = --mpSubformulas->end();
                return result;
            }

            /**
             * @return A constant iterator to the last element. Note, that it presumes that there is at least one sub-formula.
             */
            const_iterator last() const
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                const_iterator result = --mpSubformulas->end();
                return result;
            }

            /**
             * @return A pointer to the last sub-formula of this formula.
             */
            Formula* back()
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                return mpSubformulas->back();
            }

            /**
             * @return A pointer to the last sub-formula of this formula.
             */
            const Formula* back() const
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                return mpSubformulas->back();
            }

            /**
             * @return A reference to the last sub-formula of this formula.
             */
            const Formula& rBack() const
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                return *mpSubformulas->back();
            }

           /**
             * Constructs a new constraint and adds it to the shared constraint pool, if it is not yet a member. If it is a
             * member, this will be returned instead of a new constraint.
             * Note, that the left-hand side of the constraint is simplified and normalized, hence it is
             * not necessarily equal to the given left-hand side. The same holds for the relation symbol.
             * However, it is assured that the returned constraint has the same solutions as
             * the expected one.
             * @param _lhs The left-hand side of the constraint.
             * @param _rel The relation symbol of the constraint.
             * @param _variables An over-approximation of the variables which occur on the left-hand side.
             * @return The constructed constraint.
             */
            static const Constraint* newBound( const carl::Variable& _var, const Constraint::Relation _rel, const Rational& _bound )
            {
                return mpConstraintPool->newBound( _var, _rel, _bound );
            }

            /**
             * Constructs a new constraint and adds it to the shared constraint pool, if it is not yet a member. If it is a
             * member, this will be returned instead of a new constraint.
             * Note, that the left-hand side of the constraint is simplified and normalized, hence it is
             * not necessarily equal to the given left-hand side. The same holds for the relation symbol.
             * However, it is assured that the returned constraint has the same solutions as
             * the expected one.
             * @param _lhs The left-hand side of the constraint.
             * @param _rel The relation symbol of the constraint.
             * @param _variables An over-approximation of the variables which occur on the left-hand side.
             * @return The constructed constraint.
             */
            static const Constraint* newConstraint( const Polynomial& _lhs, const Constraint::Relation _rel )
            {
                return mpConstraintPool->newConstraint( _lhs, _rel );
            }

            /**
             * Constructs a new real variable.
             * @param _name The intended name of the real variable.
             * @return The constructed real variable.
             */
            static carl::Variable newRealVariable( const std::string& _name )
            {
                return mpConstraintPool->newArithmeticVariable( _name, carl::VariableType::VT_REAL );
            }
            
            /**
             * Constructs a new arithmetic variable of the given domain.
             * @param _name The intended name of the arithmetic variable.
             * @param _domain The domain of the arithmetic variable.
             * @return The constructed arithmetic variable.
             */
            static carl::Variable newArithmeticVariable( const std::string& _name, carl::VariableType _domain )
            {
                return mpConstraintPool->newArithmeticVariable( _name, _domain );
            }

            /**
             * Constructs a new Boolean variable.
             * @param _name The intended name of the variable.
             * @return A pointer to the name of the constructed Boolean variable.
             */
            static const std::string* newBooleanVariable( const std::string& _name )
            {
                return mpConstraintPool->newBooleanVariable( _name );
            }

            /**
             * @return A constant reference to the shared constraint pool.
             */
            static const ConstraintPool& constraintPool()
            {
                return *mpConstraintPool;
            }

            /**
             * Generates a fresh real variable and returns its identifier.
             * @return The fresh real variable.
             */
            static carl::Variable newAuxiliaryRealVariable()
            {
                return mpConstraintPool->newAuxiliaryRealVariable();
            }

            /**
             * Generates a fresh real variable and returns its identifier.
             * @param _varName The dedicated name of the real variable.
             * @return The fresh real variable.
             */
            static carl::Variable newAuxiliaryRealVariable( const std::string& _varName )
            {
                return mpConstraintPool->newAuxiliaryRealVariable( _varName );
            }
            
            /**
             * Generates a fresh Boolean variable and returns its identifier.
             * @return The identifier of a fresh Boolean variable.
             */
            static const std::string* newAuxiliaryBooleanVariable()
            {
                return mpConstraintPool->newAuxiliaryBooleanVariable();
            }

            /**
             * @return true, if this formula is a Boolean atom.
             */
            bool isAtom() const
            {
                return (mType == CONSTRAINT || mType == BOOL || mType == FFALSE || mType == TTRUE);
            }

            /**
             * @return true, if the outermost operator of this formula is Boolean;
             *          false, otherwise.
             */
            bool isBooleanCombination() const
            {
                return (mType == AND || mType == OR || mType == NOT || mType == IMPLIES || mType == IFF || mType == XOR);
            }
            
            /**
             * @return true, if this formula is a conjunction of constraints;
             *          false, otherwise.
             */
            bool isConstraintConjunction() const
            {
                if( PROP_IS_PURE_CONJUNCTION <= proposition() )
                    return !(PROP_CONTAINS_BOOLEAN <= proposition());
                else
                    return false;
            }

            /**
             * @return true, if this formula is a conjunction of real constraints;
             *          false, otherwise.
             */
            bool isRealConstraintConjunction() const
            {
                if( PROP_IS_PURE_CONJUNCTION <= proposition() )
                    return (!(PROP_CONTAINS_INTEGER_VALUED_VARS <= proposition()) && !(PROP_CONTAINS_BOOLEAN <= proposition()));
                else
                    return false;
            }

            /**
             * @param _formula The pointer to the formula for which to check whether it points to a sub-formula
             *                  of this formula.
             * @return true, the given pointer to a formula points to a sub-formula of this formula;
             *          false, otherwise.
             */
            bool contains( const Formula* const _formula ) const
            {
                if( isBooleanCombination() )
                    return (std::find( mpSubformulas->begin(), mpSubformulas->end(), _formula ) != mpSubformulas->end());
                return false;
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
                
            /**
             * Sets this formulas father to the given formula.
             * @param _father The father to be of this formula.
             */
            void setFather( Formula* _father )
            {
                assert( mpFather == NULL );
                mpFather = _father;
            }

            /**
             * Removes the last sub-formula of this formula.
             */
            void pop_back()
            {
                assert( isBooleanCombination() );
                Formula* pSubForm = mpSubformulas->back();
                mpSubformulas->pop_back();
                delete pSubForm;
                mPropositionsUptodate = false;
            }

            /**
             * Removes the first sub-formula of this formula.
             */
            void pop_front()
            {
                assert( isBooleanCombination() );
                Formula* pSubForm = mpSubformulas->front();
                mpSubformulas->pop_front();
                delete pSubForm;
                mPropositionsUptodate = false;
            }

            /**
             * Erases the sub-formula at the given position of this formula.
             * @param _subformula The position of the sub-formula to erase.
             * @return The position after the erased element.
             */
            iterator erase( iterator _subformula )
            {
                assert( isBooleanCombination() );
                assert( _subformula != mpSubformulas->end() );
                Formula* pSubFormula = *_subformula;
                iterator result = mpSubformulas->erase( _subformula );
                delete pSubFormula;
                mPropositionsUptodate = false;
                return result;
            }

            /**
             * Prunes the last sub-formula off this formula.
             * @return The sub-formula which has been pruned off.
             */
            Formula* pruneBack()
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                Formula* result = mpSubformulas->back();
                result->mpFather = NULL;
                mpSubformulas->pop_back();
                mPropositionsUptodate = false;
                return result;
            }

            /**
             * Prunes the first sub-formula off this formula.
             * @return The sub-formula which has been pruned off.
             */
            Formula* pruneFront()
            {
                assert( isBooleanCombination() );
                assert( !mpSubformulas->empty() );
                Formula* result = mpSubformulas->front();
                result->mpFather = NULL;
                mpSubformulas->pop_front();
                mPropositionsUptodate = false;
                return result;
            }
            
            /**
             * Prunes the sub-formula at the given position off this formula.
             * @param _subformula The position of the sub-formula to prune.
             * @return The position after the sub-formula which has been pruned off.
             */
            iterator prune( iterator _subformula )
            {
                assert( isBooleanCombination() );
                assert( _subformula != mpSubformulas->end() );
                mPropositionsUptodate = false;
                return mpSubformulas->erase( _subformula );
            }
            
            /**
             * Collects all constraint occurring in this formula.
             * @param _constraints The container to insert the constraint into.
             */
            void getConstraints( std::vector<const Constraint*>& _constraints ) const
            {
                if( mType == CONSTRAINT )
                    _constraints.push_back( mpConstraint );
                else if( mType == AND || mType == OR || mType == NOT || mType == IFF || mType == XOR || mType == IMPLIES )
                    for( const_iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                        (*subFormula)->getConstraints( _constraints );
            }

            /**
             * Replaces the content of this formula by the content of the given formula and
             * deletes the given formula and the old content afterwards.
             * @param _formula The formula to copy.
             */
            void copyAndDelete( Formula* _formula );
            
            /**
             * Adds the given formula as the last sub-formula of this formula.
             * @param _formula The formula to add.
             */
            void addSubformula( Formula* _formula );
            
            /**
             * Replaces the sub-formula at the given position by the given formula.
             * @param _toReplace The position of the sub-formula to replace.
             * @param _replacement The formula replacing the given sub-formula.
             * @return An iterator to the changed sub-formula.
             */
            iterator replace( iterator _toReplace, Formula* _replacement );

            /**
             * Gets the propositions of this formula. It updates and stores the propositions
             * if they are not up to date, hence this method is quite efficient.
             * @return The bit vector representing the conditions of this formula.
             */
            Condition getPropositions();
            
        private:

            /**
             * Adds the propositions of the given constraint to the propositions of this formula.
             * @param _constraint The constraint to add propositions for.
             */
            void addConstraintPropositions( const Constraint& _constraint );
            
        public:
            
            /**
             * Gives the string representation of this formula.
             * @param _withActivity A flag which indicates whether to add the formula's activity to the result.
             * @param _resolveUnequal A switch which indicates how to represent the relation symbol for unequal. 
             *                         (for further description see documentation of Constraint::toString( .. ))
             * @param _init The initial string of every row of the result.
             * @param _oneline A flag indicating whether the formula shall be printed on one line.
             * @param _infix A flag indicating whether to print the formula in infix or prefix notation.
             * @param _friendlyNames A flag that indicates whether to print the variables with their internal representation (false)
             *                        or with their dedicated names.
             * @return The resulting string representation of this formula.
             */
            std::string toString( bool _withActivity = false, unsigned _resolveUnequal = 0, const std::string _init = "", bool _oneline = true, bool _infix = false, bool _friendlyNames = true ) const; 
            
            /**
             * The output operator of a formula.
             * @param _out The stream to print on.
             * @param _init
             */
            friend std::ostream& operator<<( std::ostream& _out, const Formula& _formula );
            
            /**
             * Prints the propositions of this formula.
             * @param _out The stream to print on.
             * @param _init The string to print initially in every row.
             */
            void printProposition( std::ostream& _out = std::cout, const std::string _init = "" ) const;
            
            /**
             * @param _withVariables A flag indicating whether the variables shall be displayed before the formula.
             * @return A string which represents this formula in the input format of the tool Redlog.
             */
            std::string toRedlogFormat( bool _withVariables = true ) const;
            
            /**
             * Gets a string, which represents all variables occurring in this formula in a row, separated by the given separator.
             * @param _separator The separator between the variables.
             * @param _variableIds Maps variable names to names, which shall be used instead in the result.
             * @return The string, which represents all variables occurring in this formula in a row, separated by the given separator.
             */
            std::string variableListToString( std::string _separator = ",", const std::unordered_map<std::string, std::string>& _variableIds = std::unordered_map<std::string, std::string>() ) const;
            
            /**
             * @param _type The formula type to get the string representation for.
             * @return The string representation of the given type.
             */
            static std::string FormulaTypeToString( Type _type );
            
            /**
             * Resolves the outermost negation of the given formula.
             * @param _formula The formula to resolve the negation for.
             * @param _keepConstraints A flag indicating whether to change constraints in order 
             * to resolve the negation in front of them, or to keep the constraints and leave 
             * the negation.
             */
            static bool resolveNegation( Formula& _formula, bool _keepConstraints = true );
            
            /**
             * Transforms the given formula to conjunctive normal form (CNF).
             * @param _formula The formula to transform to CNF.
             * @param _keepConstraints A flag indicating whether to keep the constraints as they are, or to
             *                          resolve constraints p!=0 to (or p<0 p>0) and to resolve negations in
             *                          front of constraints, e.g., (not p<0) gets p>=0.
             */
            static void toCNF( Formula& _formula, bool _keepConstraints = true );
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
