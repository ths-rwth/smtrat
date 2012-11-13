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
 * @file ConstraintPool.h
 *
 * @author Florian Corzilius
 * @author Sebastian Junges
 * @author Ulrich Loup
 * @version 2012-10-13
 */
#include "Constraint.h"
#include <unordered_set>

#ifndef CONSTRAINTPOOL_H
#define CONSTRAINTPOOL_H

namespace smtrat
{
    struct constraintEqual
    {
        bool operator ()( const Constraint* const _constraintA, const Constraint* const _constraintB ) const
        {
            if( _constraintA->relation() == _constraintB->relation() )
            {
                return _constraintA->lhs().is_equal( _constraintB->lhs() );
            }
            return false;
        }
    };

    struct constraintHash
    {
        size_t operator ()( const Constraint* const _constraint ) const
        {
            return _constraint->lhs().gethash() * 6 + _constraint->relation();
        }
    };

    struct constraintPointerCmp
    {
        bool operator ()( const Constraint* const _constraintA, const Constraint* const _constraintB ) const
        {
            return ( (*_constraintA) < (*_constraintB) );
        }
    };

    typedef std::unordered_set<const Constraint*, constraintHash, constraintEqual> fastConstraintSet;
    typedef fastConstraintSet::const_iterator                                      fcs_const_iterator;

    class ConstraintPool
    {
        private:

            // Members:

            /// id allocator
            unsigned mIdAllocator;
            /// A counter for the auxiliary Booleans defined in this formula.
            unsigned mAuxiliaryBooleanCounter;
            /// A counter for the auxiliary Booleans defined in this formula.
            unsigned mAuxiliaryRealCounter;
            /// The prefix for any auxiliary Boolean defined in this formula.
            const std::string mAuxiliaryBooleanNamePrefix;
            /// The prefix for any auxiliary Boolean defined in this formula.
            const std::string mAuxiliaryRealNamePrefix;
            /// the symbol table containing the variables of all constraints
            GiNaC::symtab mAllRealVariables;
            ///
            std::set<std::string> mAllBooleanVariables;
            /// for each string representation its constraint (considering all constraints of which the manager has already been informed)
            fastConstraintSet mAllConstraints;
            /// variable-free constraints
            fastConstraintSet mAllVariableFreeConstraints;

            // Methods:

            static std::string prefixToInfix( const std::string& );

            bool hasNoOtherVariables( const GiNaC::ex& _expression ) const
            {
                GiNaC::lst substitutionList = GiNaC::lst();
                for( GiNaC::symtab::const_iterator var = mAllRealVariables.begin(); var != mAllRealVariables.end(); ++var )
                {
                    substitutionList.append( GiNaC::ex_to<GiNaC::symbol>( var->second ) == 0 );
                }
                return _expression.subs( substitutionList ).info( GiNaC::info_flags::rational );
            }

        public:

            ConstraintPool( unsigned _capacity = 10000 ):
                mIdAllocator( 1 ),
                mAuxiliaryBooleanCounter( 0 ),
                mAuxiliaryRealCounter( 0 ),
                mAuxiliaryBooleanNamePrefix( "h_b_" ),
                mAuxiliaryRealNamePrefix( "h_r_" ),
                mAllRealVariables(),
                mAllBooleanVariables(),
                mAllConstraints(),
                mAllVariableFreeConstraints()
            {
                mAllConstraints.reserve( _capacity );
                mIdAllocator = 1;
            }

            virtual ~ConstraintPool()
            {
                while( !mAllConstraints.empty() )
                {
                    const Constraint* pCons = *mAllConstraints.begin();
                    mAllConstraints.erase( mAllConstraints.begin() );
                    delete pCons;
                }
                while( !mAllVariableFreeConstraints.empty() )
                {
                    const Constraint* pCons = *mAllVariableFreeConstraints.begin();
                    mAllVariableFreeConstraints.erase( mAllVariableFreeConstraints.begin() );
                    delete pCons;
                }
            }

            fcs_const_iterator begin() const
            {
                return mAllConstraints.begin();
            }

            fcs_const_iterator end() const
            {
                return mAllConstraints.end();
            }

            unsigned size() const
            {
                return mAllConstraints.size();
            }

            void clear()
            {
                mAllRealVariables.clear();
                mAllConstraints.clear();
                mAllVariableFreeConstraints.clear();
                mIdAllocator = 1;
            }

            const GiNaC::symtab& variables() const
            {
                return mAllRealVariables;
            }

            const std::set<std::string>& booleanVariables() const
            {
                return mAllBooleanVariables;
            }

            unsigned maxLenghtOfVarName() const
            {
                unsigned result = 0;
                for( GiNaC::symtab::const_iterator var = mAllRealVariables.begin(); var != mAllRealVariables.end(); ++var )
                {
                    if( var->first.size() > result ) result = var->first.size();
                }
                for( std::set<std::string>::const_iterator var = mAllBooleanVariables.begin(); var != mAllBooleanVariables.end(); ++var )
                {
                    if( var->size() > result ) result = var->size();
                }
                return result;
            }

            const Constraint* newConstraint( const GiNaC::ex& _lhs, const Constraint_Relation _rel, const GiNaC::symtab& _variables )
            {
                assert( hasNoOtherVariables( _lhs ) );
                Constraint* constraint;
                if( _rel == CR_GREATER )
                {
                    constraint = new Constraint( -_lhs, CR_LESS, _variables, mIdAllocator );
                }
                else if( _rel == CR_GEQ )
                {
                    constraint = new Constraint( -_lhs, CR_LEQ, _variables, mIdAllocator );
                }
                else
                {
                    constraint = new Constraint( _lhs, _rel, _variables, mIdAllocator );
                }
                if( constraint->isConsistent() == 2 )
                {
                    std::pair<fastConstraintSet::iterator, bool> iterBoolPair = mAllConstraints.insert( constraint );
                    if( !iterBoolPair.second )
                    {
                        delete constraint;
                    }
                    else
                    {
                        ++mIdAllocator;
                        constraint->collectProperties();
                    }
                    return *iterBoolPair.first;
                }
                else
                {
                    std::pair<fastConstraintSet::iterator, bool> iterBoolPair = mAllVariableFreeConstraints.insert( constraint );
                    if( !iterBoolPair.second )
                    {
                        delete constraint;
                    }
                    return *iterBoolPair.first;
                }
            }

            const Constraint* newConstraint( const GiNaC::ex& _lhs, const GiNaC::ex& _rhs, const Constraint_Relation _rel, const GiNaC::symtab& _variables )
            {
                assert( hasNoOtherVariables( _lhs ) && hasNoOtherVariables( _rhs ) );
                Constraint* constraint;
                if( _rel == CR_GREATER )
                {
                    constraint = new Constraint( -_lhs, -_rhs, CR_LESS, _variables, mIdAllocator );
                }
                else if( _rel == CR_GEQ )
                {
                    constraint = new Constraint( -_lhs, -_rhs, CR_LEQ, _variables, mIdAllocator );
                }
                else
                {
                    constraint = new Constraint( _lhs, _rhs, _rel, _variables, mIdAllocator );
                }
                if( constraint->isConsistent() == 2 )
                {
                    std::pair<fastConstraintSet::iterator, bool> iterBoolPair = mAllConstraints.insert( constraint );
                    if( !iterBoolPair.second )
                    {
                        delete constraint;
                    }
                    else
                    {
                        ++mIdAllocator;
                        constraint->collectProperties();
                    }
                    return *iterBoolPair.first;
                }
                else
                {
                    std::pair<fastConstraintSet::iterator, bool> iterBoolPair = mAllVariableFreeConstraints.insert( constraint );
                    if( !iterBoolPair.second )
                    {
                        delete constraint;
                    }
                    return *iterBoolPair.first;
                }
            }

            const Constraint* newConstraint( const std::string& _stringrep, const bool = true, const bool = true );

            GiNaC::ex newVariable( const std::string& _name )
            {
                GiNaC::symtab::iterator var = mAllRealVariables.find( _name );
                if( var != mAllRealVariables.end() )
                {
                    assert( false );
                    return var->second;
                }
                else
                {
                    GiNaC::parser reader( mAllRealVariables );
                    GiNaC::ex var = reader( _name );
                    return mAllRealVariables.insert( std::pair<const std::string, GiNaC::ex>( _name, var ) ).first->second;
                }
            }

            std::pair<std::string,GiNaC::ex> newAuxiliaryReal()
            {
                std::stringstream out;
                out << mAuxiliaryRealNamePrefix << mAuxiliaryRealCounter++;
                assert( mAllRealVariables.find( out.str() ) == mAllRealVariables.end() );
                GiNaC::parser reader( mAllRealVariables );
                GiNaC::ex var = reader( out.str() );
                return *mAllRealVariables.insert( std::pair<const std::string, GiNaC::ex>( out.str(), var ) ).first;
            }

            void newAuxiliaryBoolean( const std::string& _name )
            {
                assert( mAllBooleanVariables.find( _name ) == mAllBooleanVariables.end() );
                mAllBooleanVariables.insert( _name );
            }

            std::string newAuxiliaryBoolean()
            {
                std::stringstream out;
                out << mAuxiliaryBooleanNamePrefix << mAuxiliaryBooleanCounter++;
                mAllBooleanVariables.insert( out.str() );
                return out.str();
            }

            void print( std::ostream& _out = std::cout ) const
            {
                _out << "---------------------------------------------------" << std::endl;
                _out << "Constraint pool:" << std::endl;
                for( fcs_const_iterator constraint = mAllConstraints.begin();
                     constraint != mAllConstraints.end(); ++constraint )
                {
                    _out << "    " << **constraint << std::endl;
                }
                _out << "---------------------------------------------------" << std::endl;
            }

            int maxDegree() const;
            unsigned nrNonLinearConstraints() const;
    };
}    // namespace smtrat

#endif   /* CONSTRAINTPOOL_H */
