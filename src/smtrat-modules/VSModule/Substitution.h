/**
 * Class to create a substitution object.
 * @author Florian Corzilius
 * @since 2010-05-11
 * @version 2013-10-23
 */

#pragma once

#include "Condition.h"

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

namespace smtrat {
namespace vs
{

    class Substitution
    {
        public:
            /// The type of a substitution.
            enum Type { NORMAL, PLUS_EPSILON, MINUS_INFINITY, PLUS_INFINITY, INVALID };
        
        private:
            // Members.
            
            /// The variable to substitute.
            carl::Variable mVariable;
            /// The pointer (if != NULL) to the square root term to substitute the variable for.
            smtrat::SqrtEx* mpTerm;
            /// The type.
            Type mType;
            /// The variables occurring in the term to substitute for.
            mutable carl::Variables* mpTermVariables;
            /// The conditions from which this substitution has been originated. (e.g. [x -> 2] could have had the origins {x-2<=0, x^2-4=0})
            carl::PointerSet<Condition> mOriginalConditions;
            /// The side conditions, which have to hold to make this substitution valid. (e.g. [x -> 1/a] has the side condition {a!=0})
            smtrat::ConstraintsT mSideCondition;

        public:

            /**
             * Constructs a substitution with no square root term to map to.
             * @param _variable The variable to substitute of the substitution to construct.
             * @param _type The type of the substitution of the substitution to construct.
             * @param _oConditions The original conditions of the substitution to construct.
             * @param _sideCondition The side conditions of the substitution to construct.
             */
            Substitution( const carl::Variable& _variable, const Type& _type, carl::PointerSet<Condition>&& _oConditions, smtrat::ConstraintsT&& _sideCondition = smtrat::ConstraintsT() );
            
            /**
             * Constructs a substitution with a square root term to map to.
             * @param _variable The variable to substitute of the substitution to construct.
             * @param _term The square root term to which the variable maps to.
             * @param _type The type of the substitution of the substitution to construct.
             * @param _oConditions The original conditions of the substitution to construct.
             * @param _sideCondition The side conditions of the substitution to construct.
             */
            Substitution( const carl::Variable&, const smtrat::SqrtEx& _term, const Type& _type, carl::PointerSet<Condition>&& _oConditions, smtrat::ConstraintsT&& _sideCondition = smtrat::ConstraintsT() );
            
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
            const smtrat::SqrtEx& term() const
            {
                return *mpTerm;
            }
            
            /**
             * Sets the substitution term to the given rational.
             * @param _value The value to set the substitution term to.
             */
            void setTerm( const smtrat::Rational& _value )
            {
                assert( mType == Type::MINUS_INFINITY );
                *mpTerm = smtrat::SqrtEx( smtrat::Poly( _value ) );
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
            const Type& type() const
            {
                return mType;
            }

            /**
             * @return A reference to the original conditions of this substitution.
             */
            carl::PointerSet<Condition>& rOriginalConditions()
            {
                return mOriginalConditions;
            }

            /**
             * @return A constant reference to the original conditions of this substitution.
             */
            const carl::PointerSet<Condition>& originalConditions() const
            {
                return mOriginalConditions;
            }

            /**
             * @return A constant reference to the side condition of this substitution.
             */
            const smtrat::ConstraintsT& sideCondition() const
            {
                return mSideCondition;
            }
            
            /**
             * @return A constant reference to the variables occurring in the substitution term.
             */
            const carl::Variables& termVariables() const
            {
                if( mpTermVariables == NULL )
                {
                    mpTermVariables = new carl::Variables();
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
             * Prints this substitution on the given stream, with some additional information.
             * @param _withOrigins A flag indicating whether to print also the origins of this substitution.
             * @param _withSideConditions A flag indication whether to also the side conditions of this substitution.
             * @param _out The stream to print on.
             * @param _init The string to print at the beginning of every row.
             */
            void print( bool _withOrigins = false, bool _withSideConditions = false, std::ostream& _out = std::cout, const std::string& _init = "" ) const;
    };
	/**
	 * Prints the given substitution on the given output stream.
	 * @param _out The output stream, on which to write.
	 * @param _substitution  The substitution to print.
	 * @return The output stream after printing the substitution on it.
	 */
	std::ostream& operator<<(std::ostream& os, const Substitution& s);

}    // end namspace vs
}

namespace std
{
    template<>
    struct hash<smtrat::vs::Substitution>
    {
    public:
        size_t operator()( const smtrat::vs::Substitution& _substitution ) const 
        {
            return ((hash<smtrat::SqrtEx>()(_substitution.term()) << 7) ^ hash<carl::Variable>()( _substitution.variable() ) << 2) ^ _substitution.type();
        }
    };
} // namespace std

namespace smtrat {
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
    using SubstitutionFastPointerMap = std::unordered_map<const smtrat::Poly*, T, substitutionPointerHash, substitutionPointerEqual>;
}
}