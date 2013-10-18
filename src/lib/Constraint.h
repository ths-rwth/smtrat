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
 * Constraint.h
 * @author Florian Corzilius
 * @author Sebastian Junges
 * @author Ulrich Loup
 * @since 2010-04-26
 * @version 2013-03-27
 */


#ifndef SMTRAT_TS_CONSTRAINT_H
#define SMTRAT_TS_CONSTRAINT_H

//#define SMTRAT_TS_CONSTRAINT_SIMPLIFIER
//#define NDEBUG

#include <iostream>
#include <cstring>
#include <sstream>
#include <assert.h>
#include <mutex>
#include "Common.h"
#include "config.h"

namespace smtrat
{
    /**
     * Class to create a constraint object.
     * @author Florian Corzilius
     * @since 2010-04-26
     * @version 2011-12-05
     */
    class Constraint
    {
        friend class ConstraintPool;
        
        public:
            enum Relation { EQ = 0, NEQ = 1, LESS = 2, GREATER = 3, LEQ = 4, GEQ = 5 };

        private:
            // Attributes.
            unsigned             mID;
            unsigned             mFirstHash;
            unsigned             mSecondHash;
            unsigned             mHash;
            bool                 mIsNeverPositive;
            bool                 mIsNeverNegative;
            bool                 mIsNeverZero;
            Relation             mRelation;
            Polynomial           mLhs;
            Factorization        mFactorization;
            mutable std::mutex   mMutexCoefficients;
            Variables            mVariables;
            mutable VarInfoMap   mVarInfoMap;

            // Constructors.
            Constraint();
            Constraint( const Polynomial&, const Relation, unsigned = 0 );
            Constraint( const Constraint&, bool = false );

            // Destructor.
            ~Constraint();
            
        public:

            static std::recursive_mutex mMutex;

            // Methods.
            const Polynomial& lhs() const
            {
                return mLhs;
            }

            const Variables& variables() const
            {
                return mVariables;
            }

            Relation relation() const
            {
                return mRelation;
            }

            unsigned id() const
            {
                return mID;
            }

            unsigned& rId()
            {
                return mID;
            }

            unsigned firstHash() const
            {
                return mFirstHash;
            }

            unsigned secondHash() const
            {
                return mSecondHash;
            }

            unsigned hash() const
            {
                return mHash;
            }

            bool hasFactorization() const
            {
                return (mFactorization.size() > 1);
            }

            const Factorization& factorization() const
            {
                return mFactorization;
            }

            Rational constantPart() const
            {
                if( mLhs.hasConstantTerm() )
                    return mLhs.trailingTerm()->coeff();
                else
                    return Rational( 0 );
            }

            unsigned maxDegree( const carl::Variable& _variable ) const
            {
                return mVarInfoMap.getVarInfo( _variable )->maxDegree();
            }

            unsigned minDegree( const carl::Variable& _variable ) const
            {
                return mVarInfoMap.getVarInfo( _variable )->minDegree();
            }

            unsigned occurences( const carl::Variable& _variable ) const
            {
                return mVarInfoMap.getVarInfo( _variable )->occurence();
            }

            bool constraintRelationIsStrict( Relation rel ) const
            {
                return (rel == NEQ || rel == LESS || rel == GREATER);
            }
            
            /**
             * Checks if the given variable occurs in the constraint.
             * @param _var  The variable to check for.
             * @return true, if the given variable occurs in the constraint;
             *          false, otherwise.
             */
            bool hasVariable( const carl::Variable& _var ) const
            {
                return mVariables.find( _var ) != mVariables.end();
            }
            
            /**
             * Checks if this constraints contains an integer valued variable.
             * @return true, if it does;
             *          false, otherwise.
             */
            bool hasIntegerValuedVariable() const
            {
                for( auto var = mVariables.begin(); var != mVariables.end(); ++var )
                {
                    if( var->getType() == carl::VariableType::VT_INT )
                        return true;
                }
                return false;
            }
            
            /**
             * Checks if this constraints contains an real valued variable.
             * @return true, if it does;
             *          false, otherwise.
             */
            bool hasRealValuedVariable() const
            {
                for( auto var = mVariables.begin(); var != mVariables.end(); ++var )
                {
                    if( var->getType() == carl::VariableType::VT_REAL )
                        return true;
                }
                return false;
            }

            static bool evaluate( const Rational&, Relation );
            unsigned isConsistent() const;
            unsigned consistentWith( const EvalDoubleIntervalMap& ) const;
            unsigned satisfiedBy( std::map<carl::Variable,Rational>& ) const;
            bool operator <( const Constraint& ) const;
            bool operator ==( const Constraint& ) const;
            friend std::ostream& operator <<( std::ostream&, const Constraint& );
            Polynomial coefficient( const carl::Variable&, unsigned ) const;
            void collectProperties();
            Constraint* simplify();
            void init();
            std::string toString( unsigned _unequalSwitch = 0, bool _infix = true, bool _friendlyVarNames = true ) const;
            void printProperties( std::ostream& = std::cout, bool = true ) const;
            static Relation invertRelation( const Relation _rel );
            static signed compare( const Constraint*, const Constraint* );
    };

    typedef std::vector<const Constraint*>                                vec_const_pConstraint;
    typedef std::vector<std::set<const Constraint*> >                     vec_set_const_pConstraint;
    typedef std::map<const Constraint* const , vec_set_const_pConstraint> constraintOriginsMap;
    struct constraintPointerComp
    {
        bool operator ()( const Constraint* const pConstraintA, const Constraint* const pConstraintB ) const
        {
            return (*pConstraintA) < (*pConstraintB);
        }
    };

    struct constraintIdComp
    {
        bool operator() (const Constraint* const pConstraintA, const Constraint* const pConstraintB ) const
        {
            return pConstraintA->id() < pConstraintB->id();
        }
    };

    typedef std::set< const Constraint*, constraintPointerComp > ConstraintSet;
}    // namespace smtrat

namespace std
{
    template<>
    class hash<smtrat::Constraint>
    {
    public:
        size_t operator()( const smtrat::Constraint& constraint ) const 
        {
            return (hash<smtrat::Polynomial>()( constraint.lhs() ) << 3) ^ constraint.relation();
        }
    };
} // namespace std

#ifdef SMTRAT_STRAT_PARALLEL_MODE
#define CONSTRAINT_LOCK_GUARD std::lock_guard<std::recursive_mutex> lock( smtrat::Constraint::mMutex );
#define CONSTRAINT_LOCK smtrat::Constraint::mMutex.lock();
#define CONSTRAINT_UNLOCK smtrat::Constraint::mMutex.unlock();
#else
#define CONSTRAINT_LOCK_GUARD
#define CONSTRAINT_LOCK
#define CONSTRAINT_UNLOCK
#endif

#endif
