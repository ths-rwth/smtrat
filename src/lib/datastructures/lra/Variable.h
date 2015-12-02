/**
 * @file Variable.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#pragma once

#define LRA_NO_DIVISION

#include "Bound.h"
#include "../../Common.h"
#include <sstream>
#include <iomanip>
#include <list>

namespace smtrat
{
    namespace lra
    {
        ///
        typedef size_t EntryID;
        ///
        static EntryID LAST_ENTRY_ID = 0;
        
        template<typename T1, typename T2>
        class Variable
        {
            private:
                ///
                bool mBasic;
                ///
                bool mOriginal;
                ///
                bool mInteger;
                ///
                bool mObjective;
                ///
                EntryID mStartEntry;
                ///
                size_t mSize;
                ///
                double mConflictActivity;
                ///
                union
                {
                    ///
                    size_t mPosition;
                    ///
                    typename std::list<std::list<std::pair<Variable<T1,T2>*,T2>>>::iterator mPositionInNonActives;
                };
                ///
                typename Bound<T1, T2>::BoundSet mUpperbounds;
                ///
                typename Bound<T1, T2>::BoundSet mLowerbounds;
                ///
                const Bound<T1, T2>* mpSupremum;
                ///
                const Bound<T1, T2>* mpInfimum;
                ///
                const typename Poly::PolyType* mExpression;
                ///
                Value<T1> mAssignment;
                ///
                Value<T1> mLastConsistentAssignment;
                #ifdef LRA_NO_DIVISION
                ///
                T2 mFactor;
                #endif

            public:
                /**
                 * 
                 * @param _position
                 * @param _expression
                 * @param _defaultBoundPosition
                 * @param _isInteger
                 */
                Variable( size_t _position, const typename Poly::PolyType* _expression, ModuleInput::iterator _defaultBoundPosition, bool _isInteger, bool _isObjective = false );
                
                /**
                 * 
                 * @param _positionInNonActives
                 * @param _expression
                 * @param _defaultBoundPosition
                 * @param _isInteger
                 */
                Variable( typename std::list<std::list<std::pair<Variable<T1,T2>*,T2>>>::iterator _positionInNonActives, const typename Poly::PolyType* _expression, ModuleInput::iterator _defaultBoundPosition, bool _isInteger, bool _isObjective = false );
                
                /**
                 * 
                 */
                virtual ~Variable();

                /**
                 * @return 
                 */
                const Value<T1>& assignment() const
                {
                    return mAssignment;
                }

                /**
                 * @return 
                 */
                Value<T1>& rAssignment()
                {
                    return mAssignment;
                }
                
                /**
                 * 
                 */
                void resetAssignment()
                {
                    mAssignment = mLastConsistentAssignment;
                }
                
                /**
                 * 
                 */
                void storeAssignment()
                {
                    mLastConsistentAssignment = mAssignment;
                }

                /**
                 * 
                 * @param _basic
                 */
                void setBasic( bool _basic )
                {
                    mBasic = _basic;
                }

                /**
                 * @return 
                 */
                bool isBasic() const
                {
                    return mBasic;
                }

                /**
                 * @return 
                 */
                bool isOriginal() const
                {
                    return mOriginal;
                }

                /**
                 * @return 
                 */
                bool isInteger() const
                {
                    return mInteger;
                }

                /**
                 * @return 
                 */
                bool isObjective() const
                {
                    return mObjective;
                }

                /**
                 */
                void setObjective( bool _isObjective )
                {
                    mObjective = _isObjective;
                }
                
                /**
                 * @return 
                 */
                bool isActive() const
                {
                    return !(mpInfimum->isInfinite() && mpSupremum->isInfinite());
                }
                
                /**
                 * @return 
                 */
                bool involvesEquation() const
                {
                    return !mpInfimum->isInfinite() && mpInfimum->type() == Bound<T1,T2>::EQUAL;
                }
                
                /**
                 * @return 
                 */
                EntryID startEntry() const
                {
                    return mStartEntry;
                }
                
                /**
                 * @return 
                 */
                EntryID& rStartEntry()
                {
                    return mStartEntry;
                }
                
                /**
                 * @return 
                 */
                size_t size() const
                {
                    return mSize;
                }
                
                /**
                 * @return 
                 */
                size_t& rSize()
                {
                    return mSize;
                }
                
                /**
                 * @return 
                 */
                double conflictActivity() const
                {
                    return mConflictActivity;
                }
                
                /**
                 * 
                 * @param _supremum
                 */
                void setSupremum( const Bound<T1, T2>* _supremum )
                {
                    assert( _supremum->isActive() );
                    assert( mpSupremum->isActive() );
                    if( !mpSupremum->isInfinite() )
                        --mpSupremum->pInfo()->updated;
                    ++_supremum->pInfo()->updated;
                    mpSupremum = _supremum;
                }

                /**
                 * @return 
                 */
                const Bound<T1, T2>* pSupremum() const
                {
                    assert( !mpSupremum->origins().empty() );
                    return mpSupremum;
                }

                /**
                 * @return 
                 */
                const Bound<T1, T2>& supremum() const
                {
                    assert( !mpSupremum->origins().empty() );
                    return *mpSupremum;
                }

                /**
                 * 
                 * @param _infimum
                 */
                void setInfimum( const Bound<T1, T2>* _infimum )
                {
                    assert( _infimum->isActive() );
                    assert( mpInfimum->isActive() );
                    if( !mpInfimum->isInfinite() )
                        --mpInfimum->pInfo()->updated;
                    ++_infimum->pInfo()->updated;
                    mpInfimum = _infimum;
                    updateConflictActivity();
                }

                /**
                 * @return 
                 */
                const Bound<T1, T2>* pInfimum() const
                {
                    assert( !mpInfimum->origins().empty() );
                    return mpInfimum;
                }

                /**
                 * @return 
                 */
                const Bound<T1, T2>& infimum() const
                {
                    assert( !mpInfimum->origins().empty() );
                    return *mpInfimum;
                }

                /**
                 * @return 
                 */
                size_t position() const
                {
                    return mPosition;
                }
                
                /**
                 * @param _position
                 */
                void setPosition( size_t _position )
                {
                    mPosition = _position;
                }
                
                bool isConflicting() const
                {
                    return *mpInfimum > *mpSupremum;
                }

                /**
                 * @return 
                 */
                typename std::list<std::list<std::pair<Variable<T1,T2>*,T2>>>::iterator positionInNonActives() const
                {
                    return mPositionInNonActives;
                }
                
                /**
                 * 
                 * @param _positionInNonActives
                 */
                void setPositionInNonActives( typename std::list<std::list<std::pair<Variable<T1,T2>*,T2>>>::iterator _positionInNonActives )
                {
                    mPositionInNonActives = _positionInNonActives;
                }

                /**
                 * @return 
                 */
                size_t rLowerBoundsSize()
                {
                    return mLowerbounds.size();
                }

                /**
                 * @return 
                 */
                size_t rUpperBoundsSize()
                {
                    return mUpperbounds.size();
                }

                /**
                 * @return 
                 */
                const typename Bound<T1, T2>::BoundSet& upperbounds() const
                {
                    return mUpperbounds;
                }

                /**
                 * @return 
                 */
                const typename Bound<T1, T2>::BoundSet& lowerbounds() const
                {
                    return mLowerbounds;
                }

                /**
                 * @return 
                 */
                typename Bound<T1, T2>::BoundSet& rUpperbounds()
                {
                    return mUpperbounds;
                }

                /**
                 * @return 
                 */
                typename Bound<T1, T2>::BoundSet& rLowerbounds()
                {
                    return mLowerbounds;
                }

                /**
                 * @return 
                 */
                size_t& rPosition()
                {
                    return mPosition;
                }

                /**
                 * @return 
                 */
                const typename Poly::PolyType* pExpression() const
                {
                    return mExpression;
                }

                /**
                 * @return 
                 */
                const typename Poly::PolyType& expression() const
                {
                    return *mExpression;
                }
                
                #ifdef LRA_NO_DIVISION
                /**
                 * @return 
                 */
                const T2& factor() const
                {
                    return mFactor;
                }
                
                /**
                 * @return 
                 */
                T2& rFactor()
                {
                    return mFactor;
                }
                #endif

                /**
                 * 
                 * @param _ass
                 * @return 
                 */
                unsigned isSatisfiedBy( const EvalRationalMap& _ass ) const
                {
                    typename Poly::PolyType polyTmp = mExpression->substitute( _ass );
                    if( polyTmp.isConstant() )
                        return (*mpInfimum) <= polyTmp.constantPart() && (*mpSupremum) >= polyTmp.constantPart();
					for( auto& lb : mLowerbounds )
					{
						unsigned neqSatisfied = lb->neqRepresentation().satisfiedBy( _ass );
						assert( neqSatisfied != 2 );
						if( neqSatisfied == 0 )
							return 0;
					}
					for( auto& ub : mUpperbounds )
					{
						unsigned neqSatisfied = ub->neqRepresentation().satisfiedBy( _ass );
						assert( neqSatisfied != 2 );
						if( neqSatisfied == 0 )
							return 0;
					}
                    return 2;
                }
				
				/**
                 * 
                 * @param _ass
                 * @return 
                 */
                FormulaT inConflictWith( const EvalRationalMap& _ass ) const
                {
                    typename Poly::PolyType polyTmp = mExpression->substitute( _ass );
					assert( polyTmp.isConstant() );
                    
					if( (*mpInfimum) > polyTmp.constantPart() )
						return mpInfimum->asConstraint();
					else if ( (*mpSupremum) < polyTmp.constantPart() )
						return mpSupremum->asConstraint();
					else
					{
						for( auto& lb : mLowerbounds )
						{
							unsigned neqSatisfied = lb->neqRepresentation().satisfiedBy( _ass );
							assert( neqSatisfied != 2 );
							if( neqSatisfied == 0 )
								return lb->neqRepresentation();
						}
						for( auto& ub : mUpperbounds )
						{
							unsigned neqSatisfied = ub->neqRepresentation().satisfiedBy( _ass );
							assert( neqSatisfied != 2 );
							if( neqSatisfied == 0 )
								return ub->neqRepresentation();
						}
						return FormulaT( carl::FormulaType::TRUE );
					}
                }

                /**
                 * 
                 */
                void updateConflictActivity()
                {
                    mConflictActivity = 0;
                    int counter = 0;
                    if( !mpInfimum->isInfinite() )
                    {
                        if( mpInfimum->pOrigins()->front().getType() == carl::FormulaType::AND )
                        {
                            for( const FormulaT& form : mpInfimum->pOrigins()->front().subformulas() )
                            {
                                mConflictActivity += form.activity();
                                ++counter;
                            }
                        }
                        else
                        {
                            assert( mpInfimum->pOrigins()->front().getType() == carl::FormulaType::CONSTRAINT );
                            mConflictActivity += mpInfimum->pOrigins()->front().activity();
                            ++counter;
                        }
                    }
                    if( !mpSupremum->isInfinite() )
                    {
                        if( mpSupremum->pOrigins()->front().getType() == carl::FormulaType::AND )
                        {
                            for( const FormulaT& form : mpSupremum->pOrigins()->front().subformulas() )
                            {
                                mConflictActivity += form.activity();
                                ++counter;
                            }
                        }
                        else
                        {
                            assert( mpSupremum->pOrigins()->front().getType() == carl::FormulaType::CONSTRAINT );
                            mConflictActivity += mpSupremum->pOrigins()->front().activity();
                            ++counter;
                        }
                    }
                    if( counter != 0 ) mConflictActivity /= counter;
                }

                /**
                 * 
                 * @param _val
                 * @param _position
                 * @param _constraint
                 * @param _deduced
                 * @return 
                 */
                std::pair<const Bound<T1, T2>*, bool> addUpperBound( Value<T1>* const _val, ModuleInput::iterator _position, const FormulaT& _constraint, bool _deduced = false );
                
                /**
                 * 
                 * @param _val
                 * @param _position
                 * @param _constraint
                 * @param _deduced
                 * @return 
                 */
                std::pair<const Bound<T1, T2>*, bool> addLowerBound( Value<T1>* const _val, ModuleInput::iterator _position, const FormulaT& _constraint, bool _deduced = false );
                
                /**
                 * 
                 * @param _val
                 * @param _position
                 * @param _constraint
                 * @return 
                 */
                std::pair<const Bound<T1, T2>*, bool> addEqualBound( Value<T1>* const _val, ModuleInput::iterator _position, const FormulaT& _constraint );
                
                /**
                 * 
                 * @param bound
                 * @param _position
                 * @return 
                 */
                bool deactivateBound( const Bound<T1, T2>* bound, ModuleInput::iterator _position );
                
                /**
                 * 
                 * @return 
                 */
                RationalInterval getVariableBounds() const;
                
                /**
                 * 
                 * @return 
                 */
                FormulasT getDefiningOrigins() const;
                
                /**
                 * 
                 * @param _bound
                 * @return 
                 */
                bool operator<( const Variable& _variable ) const
                {
                    if( this == &_variable )
                        return false;
                    return this->expression() < _variable.expression();
                }
                
                bool operator>( const Variable& _variable ) const
                {
                    return _variable < *this;
                }
                
                bool operator==( const Variable& _variable ) const
                {
                    return &_variable == this;
                }
                
                bool operator!=( const Variable& _variable ) const
                {
                    return !(_variable == *this);
                }

                /**
                 * 
                 * @param _out
                 */
                void print( std::ostream& _out = std::cout ) const;
                
                /**
                 * 
                 * @param _out
                 * @param _init
                 */
                void printAllBounds( std::ostream& _out = std::cout, const std::string _init = "" ) const;
        };
    }    // end namspace lra
} // end namespace smtrat

#include "Variable.tpp"
