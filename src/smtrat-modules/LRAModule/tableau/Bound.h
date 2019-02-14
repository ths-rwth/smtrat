/**
 * @file Bound.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#pragma once

#include "Value.h"
#include <smtrat-common/smtrat-common.h>
#include <stddef.h>
#include <set>

namespace smtrat
{
    namespace lra
    {
        // Forward declaration.
        template<class T1, class T2>
        class Variable;

        // Forward declaration.
        template<typename T1, typename T2>
        class Bound;

        /**
         * Stores a bound, which could be an upper "<= b" or a lower bound ">= b" for a bound value b.
         * In the case that "<= b" and ">= b" hold this bound is a so called equal bound represented by "==b".
         */
        template<typename T1, typename T2>
        class Bound
        {
            public:
            /// The type of the bound: LOWER = ">=", UPPER = "<=", EQUAL "=="
            enum Type{ LOWER, UPPER, EQUAL };

            /// A set of pointer to bounds.
            typedef carl::PointerSet<Bound<T1, T2>> BoundSet;

            /**
             * Stores some additional information for a bound.
             */
            struct Info
            {
                /**
                 * A value to store the information whether this bounds constraint has already been processed (=0), 
                 * must be processed (>0) or must be removed from consideration (<0).
                 */
                int updated;
                /**
                 * The position of this bounds constraint in a formula, if it has been processed already. Otherwise
                 * it points to the end of a formula.
                 */
                ModuleInput::iterator position;
                /// If this bound corresponds to a constraint being p<0 or p>0 for a polynomial p, we store here the constraint p!=0.
                FormulaT neqRepresentation;
                /**
                 * A flag which is only false, if this bound has been created for a constraint having != as 
                 * relation symbol, i.e. p!=0, and not yet for the constraint p<0 or p>0.
                 */
                bool exists;
                ///
                const Bound<T1, T2>* complement;
                
                Info( ModuleInput::iterator _position ):
                    updated( 0 ),
                    position( _position ),
                    neqRepresentation( FormulaT( carl::FormulaType::TRUE ) ),
                    exists( false ),
                    complement( nullptr )
                {}
            };

            private:

                ///
                bool mDeduced;
                ///
                mutable bool mMarkedAsDeleted;
                ///
                Type mType;
                ///
                const Value<T1>* mLimit;
                ///
                Variable<T1, T2>* const mVar;
                ///
                FormulaT mAsConstraint;
                ///
                std::shared_ptr<std::vector<FormulaT>> mpOrigins;
                ///
                Info* mpInfo;

            public:
                /**
                 * 
                 */
                Bound() = delete;
                
                /**
                 * 
                 * @param _limit
                 * @param _var
                 * @param _type
                 * @param _constraint
                 * @param _boundInfo
                 * @param _deduced
                 */
#ifdef __VS
                Bound(const Value<T1>* const _limit, Variable<T1, T2>* const _var, Type _type, const FormulaT& _constraint, Info* _boundInfo = NULL, bool _deduced = false);
#else
                Bound(const Value<T1>* const _limit, Variable<T1, T2>* const _var, Type _type, const FormulaT& _constraint, Bound<T1, T2>::Info* _boundInfo = NULL, bool _deduced = false);
#endif
                
                /**
                 * 
                 */
                ~Bound();

                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator >( const Value<T1>& _value ) const;
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator ==( const Value<T1>& _value ) const;
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator <( const Value<T1>& _value ) const;
                
                /**
                 * 
                 * @param _bound
                 * @return 
                 */
                bool operator <( const Bound& _bound ) const;
                
                /**
                 * 
                 * @param _bound
                 * @return 
                 */
                bool operator >( const Bound& _bound ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator ==( const T1& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator >( const T1& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator <( const T1& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator >=( const T1& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator <=( const T1& _a ) const;
                
                /**
                 * 
                 * @return 
                 */
                const std::string toString() const;
                
                /**
                 * 
                 * @param _withOrigins
                 * @param _out
                 * @param _printTypebool
                 */
                template <typename T3, typename T4> friend std::ostream& operator <<( std::ostream& _ostream, const Bound<T3, T4>& _bound );
                
                /**
                 * 
                 * @param _withOrigins
                 * @param _out
                 * @param _printTypebool
                 */
                void print( bool _withOrigins = false,  std::ostream& _out = std::cout, bool _printTypebool = false ) const;

                /**
                 * @return 
                 */
                bool deduced() const
                {
                    return mDeduced;
                }

                /**
                 * @return 
                 */
                bool markedAsDeleted() const
                {
                    return mMarkedAsDeleted;
                }

                /**
                 * @return 
                 */
                void markAsDeleted() const
                {
                    mMarkedAsDeleted = true;
                }

                /**
                 * @return 
                 */
                void unmarkAsDeleted() const
                {
                    mMarkedAsDeleted = false;
                }

                /**
                 * @return 
                 */
                const Value<T1>& limit() const
                {
                    return *mLimit;
                }

                /**
                 * @return 
                 */
                const Value<T1>* pLimit() const
                {
                    return mLimit;
                }

                /**
                 * @return 
                 */
                bool isInfinite() const
                {
                    return mLimit == NULL;
                }

                /**
                 * @return 
                 */
                Variable<T1, T2>* pVariable() const
                {
                    return mVar;
                }

                /**
                 * @return 
                 */
                const Variable<T1, T2>& variable() const
                {
                    return *mVar;
                }

                /**
                 * @return 
                 */
                Type type() const
                {
                    return mType;
                }

                /**
                 * @return 
                 */
                bool isWeak() const
                {
                    return mLimit->deltaPart() == 0;
                }

                /**
                 * @return 
                 */
                bool isUpperBound() const
                {
                    return mType != LOWER;
                }

                /**
                 * @return 
                 */
                bool isLowerBound() const
                {
                    return mType != UPPER;
                }

                /**
                 * @return 
                 */
                const FormulaT& asConstraint() const
                {
                    return mAsConstraint;
                }
                
                /**
                 * @return 
                 */
                bool hasNeqRepresentation() const
                {
                    return mpInfo->neqRepresentation.isTrue();
                }
                
                /**
                 * @return 
                 */
                const FormulaT& neqRepresentation() const
                {
                    return mpInfo->neqRepresentation;
                }
                
                /**
                 * 
                 * @param _constraint
                 */
                void setNeqRepresentation( const FormulaT& _constraint ) const
                {
                    assert( _constraint.getType() == carl::FormulaType::CONSTRAINT && _constraint.constraint().relation() == carl::Relation::NEQ );
                    if( mpInfo->neqRepresentation.isTrue() )
                    {
                        mpInfo->neqRepresentation = _constraint;
                    }
                }
                
                void resetNeqRepresentation() const
                {
                    mpInfo->neqRepresentation = FormulaT( carl::FormulaType::TRUE );
                }
                
                /**
                 * 
                 */
                void boundExists() const
                {
                    mpInfo->exists = true;
                }
                
                /**
                 * 
                 */
                void setComplement( const Bound<T1, T2>* _complement ) const
                {
                    mpInfo->complement = _complement;
                }
                
                /**
                 * 
                 */
                bool exists() const
                {
                    return mpInfo->exists;
                }

                /**
                 * @return 
                 */
                const std::shared_ptr<std::vector<FormulaT>>& pOrigins() const
                {
                    return mpOrigins;
                }

                /**
                 * @return 
                 */
                const std::vector<FormulaT>& origins() const
                {
                    return *mpOrigins;
                }

                /**
                 * @return 
                 */
                bool isActive() const
                {
                    return !mpOrigins->empty();
                }

                /**
                 * @return 
                 */
                bool isComplementActive() const
                {
                    return mpInfo->complement != nullptr && mpInfo->complement->isActive();
                }
                
                bool isUnassigned() const
                {
                    return exists() && !isActive() && !isComplementActive();
                }

                /**
                 * @return 
                 */
                Info* pInfo() const
                {
                    return mpInfo;
                }
                
                bool isSatisfied( const T1& _delta ) const
                {
                    if( isInfinite() )
                    {
                        return true;
                    }
                    const Value<T1>& ass = variable().lastConsistentAssignment();
                    switch( mType )
                    {
                        case UPPER:
                            if( isWeak() )
                            {
                                return limit().mainPart() >= ass.mainPart() + (ass.deltaPart() * _delta);
                            }
                            return limit().mainPart() + (limit().deltaPart() * _delta) > ass.mainPart() + (ass.deltaPart() * _delta);
                        case LOWER:
                            if( isWeak() )
                            {
                                return limit().mainPart() <= ass.mainPart() + (ass.deltaPart() * _delta);
                            }
                            return limit().mainPart() + (limit().deltaPart() * _delta) < ass.mainPart() + (ass.deltaPart() * _delta);
                        default:
                            assert( mType == EQUAL );
                            return limit().mainPart() == ass.mainPart() + (ass.deltaPart() * _delta);
                    }
                }

                /**
                 * @return 
                 */
                bool operator >=( const Value<T1>& v ) const
                {
                    return !((*this) < v);
                }

                /**
                 * @return 
                 */
                bool operator <=( const Value<T1>& v ) const
                {
                    return !((*this) > v);
                }
        };
    }    // end namspace lra
}    // end namspace smtrat

#include "Bound.tpp"
