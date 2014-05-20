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
 * @author Florian Corzilius
 * @author Ulrich Loup
 * @author Sebastian Junges
 * @since 2012-02-09
 * @version 2013-10-21
 */

#ifndef SMTRAT_FORMULA_H
#define SMTRAT_FORMULA_H

#include <string.h>
#include <string>
#include <set>
#include <boost/dynamic_bitset.hpp>
#include "Condition.h"
#include "modules/ModuleType.h"
#include "Assignment.h"
#include "Constraint.h"

namespace smtrat
{
    enum Type { AND, OR, NOT, IFF, XOR, IMPLIES, BOOL, CONSTRAINT, TTRUE, FFALSE };
    
    class Formula
    {
        friend class FormulaPool;
        
        public:
            typedef PointerSet<Formula>::const_iterator         const_iterator;
            typedef PointerSet<Formula>::const_reverse_iterator const_reverse_iterator;
            
        private:

            // Members.

            /// The deduction flag, which indicates, that this formula g is a direct sub-formula of
            /// a conjunction of formulas (and g f_1 .. f_n), and, that (implies (and f_1 .. f_n) g) holds.
            mutable bool mDeducted;
            /// The hash value.
            size_t mHash;
            /// The unique id.
            size_t mId;
            /// The activity for this formula, which means, how much is this formula involved in the solving procedure.
            mutable double mActivity;
            /// Some value stating an expected difficulty of solving this formula for satisfiability.
            mutable double mDifficulty;
            /// The type of this formula.
            Type mType;
            /// The content of this formula.
            union
            {
                const Formula*                            mpSubformula;
                std::pair<const Formula*,const Formula*>* mpSubformulaPair;
                PointerSet<Formula>*                      mpSubformulas;
                const Constraint*                         mpConstraint;
                carl::Variable                            mBoolean;
            };
            /// The propositions of this formula.
            Condition mProperties;
            /// A bit set indicating which Boolean Variables occur in this formula.
            boost::dynamic_bitset<> mBooleanVariables;
            
            /**
             * Constructs the formula (true), if the given bool is true and the formula (false) otherwise.
             * @param _true Specifies whether to create the formula (true) or (false).
             * @param _id A unique id of the formula to create.
             */
            Formula( bool _true, size_t _id = 0);
            
            /**
             * Constructs a formula being a Boolean variable.
             * @param _booleanVarName The pointer to the string representing the name of the Boolean variable.
             * @param _id A unique id of the formula to create.
             */
            Formula( const carl::Variable::Arg _boolean );
            
            /**
             * Constructs a formula being a constraint.
             * @param _constraint The pointer to the constraint.
             */
            Formula( const Constraint* _constraint );
            
            /**
             * Constructs the negation of the given formula: (not _subformula)
             * @param _subformula The sub-formula, which is negated by the constructed formula.
             */
            Formula( const Formula* _subformula );
            
            /**
             * Constructs an implication from the first argument to the second: (=> _subformulaA _subformulaB)
             * @param _subformulaA The premise of the formula to create.
             * @param _subformulaB The conclusion of the formula to create.
             */
            Formula( const Formula* _subformulaA, const Formula* _subformulaB );
            
            /**
             * Constructs the formula of the given type. It is either one of the atoms (true) and (false)
             * or it is a formula (boolean_op arglist), where arglist is still empty. The arguments can/have
             * to be added belatedly with, e.g., addSubformula( .. ).
             * @param _type The type of the formula to construct.
             * @param _subformulas The sub-formulas of the formula to construct.
             */
            Formula( const Type _type, PointerSet<Formula>&& _subformulas );
            
            Formula(); // Disabled
            Formula( const Formula& ); // Disabled
            
        public:

            /**
             * Destructor.
             */
            ~Formula();

            // Methods.

            /**
             * Sets the deduction flag to the given value..
             * @param _deducted The value to set the deduction flag to.
             */
            void setDeducted( bool _deducted ) const
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
            void setDifficulty( double difficulty ) const
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
            void setActivity( double _activity ) const
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
             * @return A hash value for this formula.
             */
            size_t getHash() const
            {
                return mHash;
            }
            
            /**
             * @return The unique id for this formula.
             */
            size_t getId() const
            {
                return mId;
            }

            /**
             * @return The bit-vector representing the propositions of this formula. For further information see the Condition class.
             */
            const Condition& properties() const
            {
                return mProperties;
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
            void booleanVars( std::set<carl::Variable>& _booleanVars ) const
            {
                boost::dynamic_bitset<>::size_type pos = mBooleanVariables.find_first();
                while( pos != boost::dynamic_bitset<>::npos )
                {
                    _booleanVars.insert( carl::Variable( (unsigned) pos, carl::VT_BOOL ) );
                    pos = mBooleanVariables.find_next( pos );
                }
            }
            
            const Formula* pSubformula() const
            {
                assert( mType == NOT );
                return mpSubformula;
            }
            
            const Formula& subformula() const
            {
                assert( mType == NOT );
                return *mpSubformula;
            }
            
            const Formula* pPremise() const
            {
                assert( mType == IMPLIES );
                return mpSubformulaPair->first;
            }
            
            const Formula premise() const
            {
                assert( mType == IMPLIES );
                return mpSubformulaPair->first;
            }
            
            const Formula* pConclusion() const
            {
                assert( mType == IMPLIES );
                return mpSubformulaPair->second;
            }
            
            const Formula conclusion() const
            {
                assert( mType == IMPLIES );
                return mpSubformulaPair->second;
            }

            /**
             * @return A constant reference to the list of sub-formulas of this formula. Note, that
             *          this formula has to be a Boolean combination, if you invoke this method.
             */
            const PointerSet<Formula>& subformulas() const
            {
                assert( isNary() );
                return *mpSubformulas;
            }

            /**
             * @return A pointer to the constraint represented by this formula. Note, that
             *          this formula has to be of type CONSTRAINT, if you invoke this method.
             */
            const Constraint* pConstraint() const
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
            const carl::Variable::Arg boolean() const
            {
                assert( mType == BOOL );
                return mBoolean;
            }

            /**
             * @return The number of sub-formulas of this formula.
             */
            size_t size() const
            {
                if( mType == BOOL || mType == CONSTRAINT || mType == TTRUE || mType == FFALSE || mType == NOT )
                    return 1;
                else if( mType == IMPLIES )
                    return 2;
                else
                    return mpSubformulas->size();
            }

            /**
             * @return A constant iterator to the beginning of the list of sub-formulas of this formula.
             */
            const_iterator begin() const
            {
                assert( isNary() );
                return mpSubformulas->begin();
            }

            /**
             * @return A constant iterator to the end of the list of sub-formulas of this formula.
             */
            const_iterator end() const
            {
                assert( mType == AND || mType == OR || mType == IFF || mType == XOR );
                return mpSubformulas->end();
            }

            /**
             * @return A constant reverse iterator to the beginning of the list of sub-formulas of this formula.
             */
            const_reverse_iterator rbegin() const
            {
                assert( isNary() );
                return mpSubformulas->rbegin();
            }

            /**
             * @return A constant reverse iterator to the end of the list of sub-formulas of this formula.
             */
            const_reverse_iterator rend() const
            {
                assert( isNary() );
                return mpSubformulas->rend();
            }

            /**
             * @return A pointer to the last sub-formula of this formula.
             */
            const Formula* back() const
            {
                assert( isBooleanCombination() );
                if( mType == NOT )
                    return mpSubformula;
                else if( mType == IMPLIES )
                    return mpSubformulaPair->second;
                else
                    return *(mpSubformulas->end());
            }

            /**
             * @return A reference to the last sub-formula of this formula.
             */
            const Formula& rBack() const
            {
                assert( isBooleanCombination() );
                if( mType == NOT )
                    return *mpSubformula;
                else if( mType == IMPLIES )
                    return *(mpSubformulaPair->second);
                else
                    return **(mpSubformulas->end());
            }
            
            bool propertyHolds( const Condition& _property ) const
            {
                return (mProperties | ~_property) == ~PROP_TRUE;
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
                return !isAtom();
            }

            /**
             * @return true, if the type of this formulas allows n-ary combinations of sub-formulas, for an arbitrary n.
             */
            bool isNary() const
            {
                return (mType == AND || mType == OR || mType == IFF || mType == XOR);
            }
            
            /**
             * @return true, if this formula is a conjunction of constraints;
             *          false, otherwise.
             */
            bool isConstraintConjunction() const
            {
                if( PROP_IS_PURE_CONJUNCTION <= properties() )
                    return !(PROP_CONTAINS_BOOLEAN <= properties());
                else
                    return false;
            }

            /**
             * @return true, if this formula is a conjunction of real constraints;
             *          false, otherwise.
             */
            bool isRealConstraintConjunction() const
            {
                if( PROP_IS_PURE_CONJUNCTION <= properties() )
                    return (!(PROP_CONTAINS_INTEGER_VALUED_VARS <= properties()) && !(PROP_CONTAINS_BOOLEAN <= properties()));
                else
                    return false;
            }

            /**
             * @return true, if this formula is a conjunction of integer constraints;
             *         false, otherwise.
             */
            bool isIntegerConstraintConjunction() const
            {
                if( PROP_IS_PURE_CONJUNCTION <= properties() )
                    return (!(PROP_CONTAINS_REAL_VALUED_VARS <= properties()) && !(PROP_CONTAINS_BOOLEAN <= properties()));
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
                if( isAtom() )
                    return false;
                if( mType == NOT )
                    return mpSubformula == _formula;
                else if( mType == IMPLIES )
                    return (mpSubformulaPair->first == _formula || mpSubformulaPair->second == _formula);
                else
                    return mpSubformulas->find( _formula ) != mpSubformulas->end();
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
             * @param _formula The formula to compare with.
             * @return true, if this formula and the given formula have the same id;
             *         false, otherwise.
             */
            bool operator==( const Formula& _formula ) const;
            
            /**
             * @param _formula The formula to compare with.
             * @return true, if the id of this formula is smaller than the id of the given one.
             */
            bool operator<( const Formula& _formula ) const
            {
                assert( mId != 0 );
                assert( _formula.getId() != 0 );
                return mId < _formula.getId();
            }
            
            /**
             * @param _assignment The assignment for which to check whether this formula is satisfied by it.
             * @return 0, if this formula is violated by the given assignment;
             *         1, if this formula is satisfied by the given assignment;
             *         2, otherwise.
             */
            unsigned satisfiedBy( const EvalRationalMap& _assignment ) const;
            
            /**
             * @param _assignment The assignment for which to check whether this formula is satisfied by it.
             * @return 0, if this formula is violated by the given assignment;
             *         1, if this formula is satisfied by the given assignment;
             *         2, otherwise.
             */
            unsigned satisfiedBy( const Model& _assignment ) const;
            
        private:

            /**
             * Gets the propositions of this formula. It updates and stores the propositions
             * if they are not up to date, hence this method is quite efficient.
             */
            void initProperties();
            
            /**
             * @return 
             */
            void initHash();

            /**
             * Adds the propositions of the given constraint to the propositions of this formula.
             * @param _constraint The constraint to add propositions for.
             */
            void addConstraintProperties( const Constraint& _constraint );
            
            void initBooleans();
            
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
            std::string variableListToString( std::string _separator = ",", const std::unordered_map<std::string, std::string>& _variableIds = (std::unordered_map<std::string, std::string>())) const;
            
            /**
             * @param _type The formula type to get the string representation for.
             * @return The string representation of the given type.
             */
            static std::string FormulaTypeToString( Type _type );
            
            /**
             * Resolves the outermost negation of this formula.
             * @param _keepConstraints A flag indicating whether to change constraints in order 
             * to resolve the negation in front of them, or to keep the constraints and leave 
             * the negation.
             */
            const Formula* resolveNegation( bool _keepConstraints = true ) const;
            
            /**
             * [Auxiliary method]
             * @return The formula combining the second to the last sub-formula of this formula by the 
             *         same operator as the one of this formula.
             *         Example: this = (op a1 a2 .. an) -> return = (op a2 .. an)
             *                  If n = 2, return = a2
             */
            const Formula* connectRemainingSubformulas() const;
            
            /**
             * Transforms this formula to conjunctive normal form (CNF).
             * @param _keepConstraints A flag indicating whether to keep the constraints as they are, or to
             *                          resolve constraints p!=0 to (or p<0 p>0) and to resolve negations in
             *                          front of constraints, e.g., (not p<0) gets p>=0.
             */
            const Formula* toCNF( bool _keepConstraints = true ) const;
            
            struct IteratorCompare
            {
                bool operator() ( const_iterator i1, const_iterator i2 ) const
                {
                    return (**i1) < (**i2);
                }
            };
    };
    
    std::ostream& operator<<( std::ostream& _out, const Formula& _formula );
}    // namespace smtrat

namespace std
{
    template<>
    struct hash<smtrat::Formula>
    {
    public:
        size_t operator()( const smtrat::Formula& _formula ) const 
        {
            return _formula.getHash();
        }
    };
}    // namespace std


#endif // SMTRAT_FORMULA_H
