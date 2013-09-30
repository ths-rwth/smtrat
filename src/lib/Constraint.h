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
#define VS_USE_GINAC_EXPAND
//#define VS_USE_GINAC_NORMAL


#include <vector>
#include <iostream>
#include <cstring>
#include <string.h>
#include <sstream>
#include <assert.h>
#include <mutex>
#include "config.h"
#include "carl/core/MultivariatePolynomial.h"

namespace smtrat
{
    //
    // Type and object definitions
    //

    typedef cln::cl_RA Rational;
    typedef carl::MultivariatePolynomial<Rational> Polynomial;
    typedef std::vector<Polynomial> Factorization;
    
    enum Constraint_Relation
    {
        CR_EQ = 0, CR_NEQ = 1, CR_LESS = 2, CR_GREATER = 3, CR_LEQ = 4, CR_GEQ = 5
    };

    enum Variable_Domain { BOOLEAN_DOMAIN = 0, REAL_DOMAIN = 1, INTEGER_DOMAIN = 2 };

    bool constraintRelationIsStrict( Constraint_Relation rel );
    std::string relationToString( const Constraint_Relation rel );

    typedef carl::VariablesInformation VarInfoMap;
    
    typedef std::set<carl::Variable> Variables;

    typedef std::pair< const GiNaC::ex, signed > VarDegree;

    struct varDegreeCmp
    {
        bool operator ()( const VarDegree& varDegreeA, const VarDegree& varDegreeB ) const
        {
            signed result = varDegreeA.first.compare( varDegreeB.first );
            if( result < 0 )
            {
                return true;
            }
            else if ( result == 0 )
            {
                return varDegreeA.second < varDegreeB.second;
            }
            return false;
        }
    };

    typedef std::map< VarDegree, const GiNaC::ex, varDegreeCmp > Coefficients;

    /**
     * Class to create a constraint object.
     * @author Florian Corzilius
     * @since 2010-04-26
     * @version 2011-12-05
     */
    class Constraint
    {
        private:
            /*
             * Attributes:
             */
            unsigned             mID;
            unsigned             mFirstHash;
            unsigned             mSecondHash;
            bool                 mIsNeverPositive;
            bool                 mIsNeverNegative;
            bool                 mIsNeverZero;
            bool                 mContainsRealValuedVariables;
            bool                 mContainsIntegerValuedVariables;
            unsigned             mNumMonomials;
            unsigned             mMaxMonomeDegree;
            unsigned             mMinMonomeDegree;
            Constraint_Relation  mRelation;
            Polynomial           mLhs;
            Factorization        mFactorization;
            Coefficients*        mpCoefficients;
            mutable std::mutex   mMutexCoefficients;
            Variables            mVariables;
            VarInfoMap           mVarInfoMap;

        public:

            static std::recursive_mutex mMutex;

            /*
             * Constructors:
             */
            Constraint();
            Constraint( const Polynomial&, const Constraint_Relation, unsigned = 0 );
            Constraint( const Constraint&, bool = false );

            /*
             * Destructor:
             */
            ~Constraint();

            /*
             * Methods:
             */
            const Polynomial& lhs() const
            {
                return mLhs;
            }

            const Variables& variables() const
            {
                return mVariables;
            }

            Constraint_Relation relation() const
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

            bool hasFactorization() const
            {
                return (mFactorization.size() > 1);
            }

            const Factorization& factorization() const
            {
                return mFactorization;
            }

            bool containsIntegerValuedVariable() const
            {
                return mContainsIntegerValuedVariables;
            }

            bool containsRealValuedVariable() const
            {
                return mContainsRealValuedVariables;
            }

            unsigned numMonomials() const
            {
                return mNumMonomials;
            }

            unsigned minMonomeDegree() const
            {
                return mMinMonomeDegree;
            }

            unsigned maxMonomeDegree() const
            {
                return mMaxMonomeDegree;
            }

            const Rational& constantPart() const
            {
                return mConstantPart;
            }

            unsigned maxDegree( const Variable& _variable ) const
            {
                VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
                if( varInfo != mVarInfoMap.end() )
                {
                    return varInfo->getVarInfo()->maxDegree;
                }
                else
                {
                    return 0;
                }
            }

            unsigned minDegree( const Variable& _variable ) const
            {
                VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
                if( varInfo != mVarInfoMap.end() )
                {
                    return varInfo->getVarInfo()->minDegree;
                }
                else
                {
                    return 0;
                }
            }

            unsigned occurences( const Variable& _variable ) const
            {
                VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
                if( varInfo != mVarInfoMap.end() )
                {
                    return varInfo->getVarInfo()->occurence;
                }
                else
                {
                    return 0;
                }
            }

            const VarInfo varInfo( const ex& _variable ) const
            {
                VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
                assert( varInfo != mVarInfoMap.end() ); // variable not in constraint.
                return varInfo->second;
            }

            bool constraintRelationIsStrict( Constraint_Relation rel ) const
            {
                return (rel == CR_NEQ || rel == CR_LESS || rel == CR_GREATER);
            }

            unsigned maxDegree() const
            {
                return mMaxMonomeDegree;
            }

            bool isLinear() const
            {
                return mMaxMonomeDegree < 2;
            }

            // Data access methods (read only).
            bool variable( const std::string&, GiNaC::symbol& ) const;
            bool hasVariable( const std::string& ) const;
            static bool evaluate( const numeric&, Constraint_Relation );
            unsigned isConsistent() const;
            unsigned consistentWith( const GiNaCRA::evaldoubleintervalmap& ) const;
            unsigned satisfiedBy( GiNaC::exmap& ) const;
            bool hasFinitelyManySolutionsIn( const std::string& ) const;
            GiNaC::ex coefficient( const GiNaC::ex&, int ) const;
            signed highestDegree() const;
            std::pair<GiNaC::numeric, GiNaC::numeric> cauchyBounds() const;
            std::map<const std::string, GiNaC::numeric, strCmp> linearAndConstantCoefficients() const;
            static int exCompare( const GiNaC::ex&, const GiNaC::symtab&, const GiNaC::ex&, const GiNaC::symtab& );

            // Operators.
            bool operator <( const Constraint& ) const;
            bool operator ==( const Constraint& ) const;
            friend std::ostream& operator <<( std::ostream&, const Constraint& );

            // Manipulating methods.
            static bool containsNumeric( const GiNaC::ex& );
            static bool containsNumeric( const GiNaC::ex&, GiNaC::const_iterator );
            static GiNaC::ex normalizeA( const GiNaC::ex& );
            void setBoundProperties( const GiNaC::symbol&, const GiNaC::numeric& );
            void collectProperties();
            Constraint* simplify();
            void init();

            // Printing methods.
            std::string toString( unsigned = 0 ) const;
            void print( std::ostream& _out = std::cout ) const;
            void print2( std::ostream& _out = std::cout ) const;
            void printInPrefix( std::ostream& _out = std::cout ) const;
            const std::string prefixStringOf( const GiNaC::ex& ) const;
            void printProperties( std::ostream& = std::cout ) const;
            std::string smtlibString( bool = true ) const;

            //
            static signed compare( const Constraint*, const Constraint* );
            static const Constraint* mergeConstraints( const Constraint*, const Constraint* );
            static bool combineConstraints( const Constraint*, const Constraint*, const Constraint* );
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
