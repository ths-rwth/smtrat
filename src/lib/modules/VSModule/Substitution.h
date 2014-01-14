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
 * Class to create a substitution object.
 * @author Florian Corzilius
 * @since 2010-05-11
 * @version 2013-10-23
 */

#ifndef SMTRAT_VS_SUBSTITUTION_H
#define SMTRAT_VS_SUBSTITUTION_H

#include "Condition.h"
#include "../../datastructures/vs/SqrtEx.h"

namespace vs
{

    class Substitution
    {
        public:
            // Type and object definitions.

            enum Type { NORMAL, PLUS_EPSILON, MINUS_INFINITY, INVALID };
        
        private:
            // Members.
            
            /// The variable to substitute.
            carl::Variable                 mVariable;
            /// The pointer (if != NULL) to the square root term to substitute the variable for.
            SqrtEx*                        mpTerm;
            /// The type.
            Type                           mType;
            /// The variables occurring in the term to substitute for.
            mutable smtrat::Variables*     mpTermVariables;
            /// The conditions from which this substitution has been originated. (e.g. [x -> 2] could have had the origins {x-2<=0, x^2-4=0})
            Condition::Set*                  mpOriginalConditions;
            /// The side conditions, which have to hold to make this substitution valid. (e.g. [x -> 1/a] has the side condition {a!=0})
            smtrat::PointerSet<smtrat::Constraint> mSideCondition;

        public:

            /**
             * Constructs a substitution with no square root term to map to.
             * @param _variable The variable to substitute of the substitution to construct.
             * @param _type The type of the substitution of the substitution to construct.
             * @param _oConditions The original conditions of the substitution to construct.
             * @param _sideCondition The side conditions of the substitution to construct.
             */
            Substitution( const carl::Variable& _variable, const Type& _type, const Condition::Set& _oConditions, const smtrat::PointerSet<smtrat::Constraint>& _sideCondition = smtrat::PointerSet<smtrat::Constraint>() );
            
            /**
             * Constructs a substitution with a square root term to map to.
             * @param _variable The variable to substitute of the substitution to construct.
             * @param _term The square root term to which the variable maps to.
             * @param _type The type of the substitution of the substitution to construct.
             * @param _oConditions The original conditions of the substitution to construct.
             * @param _sideCondition The side conditions of the substitution to construct.
             */
            Substitution( const carl::Variable&, const SqrtEx& _term, const Type& _type, const Condition::Set& _oConditions, const smtrat::PointerSet<smtrat::Constraint>& _sideCondition = smtrat::PointerSet<smtrat::Constraint>() );
            
            /**
             * Copy constructor.
             */
            Substitution( const Substitution& _substitution );

            /**
             * The destructor.
             */
            ~Substitution();

            /**
             * @return A constant reference to the variable this substitution substitutes.
             */
            const carl::Variable& variable() const
            {
                return mVariable;
            }
            
            /**
             * @return A constant reference to the term this substitution maps its variable to.
             */
            const SqrtEx& term() const
            {
                return *mpTerm;
            }
            
            void setTerm( const smtrat::Rational& _value )
            {
                assert( mType == Type::MINUS_INFINITY );
                *mpTerm = SqrtEx( smtrat::Polynomial( _value ) );
                mType = Type::NORMAL;
            }

            /**
             * @return A reference to the type of this substitution.
             */
            Type& rType()
            {
                return mType;
            }

            /**
             * @return A constant reference to the type of this substitution.
             */
            const Type type() const
            {
                return mType;
            }

            /**
             * @return A reference to the original conditions of this substitution.
             */
            Condition::Set& rOriginalConditions()
            {
                return *mpOriginalConditions;
            }

            /**
             * @return A constant reference to the original conditions of this substitution.
             */
            const Condition::Set& originalConditions() const
            {
                return *mpOriginalConditions;
            }

            /**
             * @return A constant reference to the side condition of this substitution.
             */
            const smtrat::PointerSet<smtrat::Constraint>& sideCondition() const
            {
                return mSideCondition;
            }
            
            const smtrat::Variables& termVariables() const
            {
                if( mpTermVariables == NULL )
                {
                    mpTermVariables = new smtrat::Variables();
                    mpTerm->constantPart().gatherVariables( *mpTermVariables );
                    mpTerm->factor().gatherVariables( *mpTermVariables );
                    mpTerm->denominator().gatherVariables( *mpTermVariables );
                    mpTerm->radicand().gatherVariables( *mpTermVariables );
                }
                return *mpTermVariables;
            }

            /**
             * @param _preferMinusInf A flag indicating whether to valuate the substitution type best or otherwise
             *                        worst.
             * @return The valuation of this substitution according to a heuristic.
             */
            unsigned valuate( bool _preferMinusInf = true ) const;

            /**
             * @param The substitution to compare with.
             * @return true, if this substitution is equal to the given substitution;
             *          false, otherwise.
             */
            bool operator==( const Substitution& ) const;
            
            /**
             * @param The substitution to compare with.
             * @return true, if this substitution is less than the given substitution;
             *          false, otherwise.
             */
//            bool operator<( const Substitution& ) const;
            
            /**
             * @param _friendlyNames A flag that indicates whether to print the variables with their internal representation (false)
             *                        or with their dedicated names.
             * @return The string representation of this substitution.
             */
            std::string toString( bool _friendlyNames = true ) const;
            
            /**
             * Prints the given substitution on the given output stream.
             * @param _out The output stream, on which to write.
             * @param _substitution  The substitution to print.
             * @return The output stream after printing the substitution on it.
             */
            friend std::ostream& operator<<( std::ostream& _out, const Substitution& _substitution );

            /**
             * Prints this substitution on the given stream, with some additional information.
             * @param _withOrigins A flag indicating whether to print also the origins of this substitution.
             * @param _withSideConditions A flag indication whether to also the side conditions of this substitution.
             * @param _out The stream to print on.
             * @param _init The string to print at the beginning of every row.
             */
            void print( bool _withOrigins = false, bool _withSideConditions = false, std::ostream& _out = std::cout, const std::string& _init = "" ) const;
    };
}    // end namspace vs

namespace std
{
    template<>
    struct hash<vs::Substitution>
    {
    public:
        size_t operator()( const vs::Substitution& _substitution ) const 
        {
            return ((hash<vs::SqrtEx>()(_substitution.term()) << 7) ^ hash<carl::Variable>()( _substitution.variable() ) << 2) ^ _substitution.type();
        }
    };
} // namespace std

namespace vs
{
    struct substitutionPointerEqual
    {
        bool operator ()( const Substitution* _substitutionA, const Substitution* _substitutionB ) const
        {
            return (*_substitutionA)==(*_substitutionB);
        }
    };

    struct substitutionPointerHash
    {
        size_t operator ()( const Substitution* _substitution ) const
        {
            if( _substitution == NULL )
                return 0;
            return std::hash<Substitution>()( *_substitution );
        }
    };
    
    template<typename T> 
    using SubstitutionFastPointerMap = std::unordered_map<const Polynomial*, T, substitutionPointerHash, substitutionPointerEqual>;
}

#endif
