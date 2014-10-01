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
 * @file Variable.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#pragma once

#include "Variable.h"

namespace smtrat
{
    namespace lra
    {
        template<typename T1, typename T2>
        Variable<T1, T2>::Variable( size_t _position, const smtrat::Polynomial* _expression, std::list<const smtrat::Formula*>::iterator _defaultBoundPosition, bool _isInteger ):
            mBasic( false ),
            mOriginal( true ),
            mInteger( _isInteger ),
            mStartEntry( LAST_ENTRY_ID ),
            mSize( 0 ),
            mConflictActivity( 0 ),
            mPosition( _position ),
            mUpperbounds(),
            mLowerbounds(),
            mExpression( _expression),
            mAssignment( T1( 0 ) ),
            mLastConsistentAssignment( mAssignment )
            #ifdef LRA_NO_DIVISION
            ,
            mFactor( 1 )
            #endif
        {
            mpSupremum = addUpperBound( NULL, _defaultBoundPosition ).first;
            mpInfimum  = addLowerBound( NULL, _defaultBoundPosition ).first;
        }
        
        template<typename T1, typename T2>
        Variable<T1, T2>::Variable( typename std::list<std::list<std::pair<Variable<T1,T2>*,T2>>>::iterator _positionInNonActives, const smtrat::Polynomial* _expression, std::list<const smtrat::Formula*>::iterator _defaultBoundPosition, bool _isInteger ):
            mBasic( true ),
            mOriginal( false ),
            mInteger( _isInteger ),
            mStartEntry( LAST_ENTRY_ID ),
            mSize( 0 ),
            mConflictActivity( 0 ),
            mPositionInNonActives( _positionInNonActives ),
            mUpperbounds(),
            mLowerbounds(),
            mExpression( _expression),
            mAssignment( T1( 0 ) ),
            mLastConsistentAssignment( mAssignment )
            #ifdef LRA_NO_DIVISION
            ,
            mFactor( 1 )
            #endif
        {
            mpSupremum = addUpperBound( NULL, _defaultBoundPosition ).first;
            mpInfimum  = addLowerBound( NULL, _defaultBoundPosition ).first;
        }

        template<typename T1, typename T2>
        Variable<T1, T2>::~Variable()
        {
            while( !mLowerbounds.empty() )
            {
                const Bound<T1, T2>* b = *mLowerbounds.begin();
                mLowerbounds.erase( mLowerbounds.begin() );
                if( b->type() != Bound<T1, T2>::EQUAL ) delete b;
            }
            while( !mUpperbounds.empty() )
            {
                const Bound<T1, T2>* b = *mUpperbounds.begin();
                mUpperbounds.erase( mUpperbounds.begin() );
                delete b;
            }
            delete mExpression;
        }

        template<typename T1, typename T2>
        std::pair<const Bound<T1, T2>*, bool> Variable<T1, T2>::addUpperBound( Value<T1>* const _val, std::list<const smtrat::Formula*>::iterator _position, const smtrat::Formula* _constraint, bool _deduced )
        {
            struct Bound<T1, T2>::Info* boundInfo = new struct Bound<T1, T2>::Info();
            boundInfo->updated = 0;
            boundInfo->position = _position;
            boundInfo->neqRepresentation = NULL;
            boundInfo->exists = false;
            const Bound<T1, T2>* newBound = new Bound<T1, T2>( _val, this, Bound<T1, T2>::UPPER, _constraint, boundInfo, _deduced );
            std::pair<typename Bound<T1, T2>::BoundSet::iterator, bool> result = mUpperbounds.insert( newBound );
            if( !result.second )
            {
                delete newBound;
            }
            return std::pair<const Bound<T1, T2>*, bool>( *result.first, result.second );
        }

        template<typename T1, typename T2>
        std::pair<const Bound<T1, T2>*, bool> Variable<T1, T2>::addLowerBound( Value<T1>* const _val, std::list<const smtrat::Formula*>::iterator _position, const smtrat::Formula* _constraint, bool _deduced )
        {
            struct Bound<T1, T2>::Info* boundInfo = new struct Bound<T1, T2>::Info();
            boundInfo->updated = 0;
            boundInfo->position = _position;
            boundInfo->neqRepresentation = NULL;
            const Bound<T1, T2>* newBound = new Bound<T1, T2>( _val, this, Bound<T1, T2>::LOWER, _constraint, boundInfo, _deduced );
            std::pair<typename Bound<T1, T2>::BoundSet::iterator, bool> result = mLowerbounds.insert( newBound );
            if( !result.second )
            {
                delete newBound;
            }
            return std::pair<const Bound<T1, T2>*, bool>( *result.first, result.second );
        }

        template<typename T1, typename T2>
        std::pair<const Bound<T1, T2>*, bool> Variable<T1, T2>::addEqualBound( Value<T1>* const _val, std::list<const smtrat::Formula*>::iterator _position, const smtrat::Formula* _constraint )
        {
            struct Bound<T1, T2>::Info* boundInfo = new struct Bound<T1, T2>::Info();
            boundInfo->updated = 0;
            boundInfo->position = _position;
            boundInfo->neqRepresentation = NULL;
            boundInfo->exists = false;
            const Bound<T1, T2>* newBound = new Bound<T1, T2>( _val, this, Bound<T1, T2>::EQUAL, _constraint, boundInfo );
            std::pair<typename Bound<T1, T2>::BoundSet::iterator, bool> result = mLowerbounds.insert( newBound );
            if( !result.second )
            {
                delete newBound;
                return std::pair<const Bound<T1, T2>*, bool>( *result.first, false );
            }
            else
            {
                std::pair<typename Bound<T1, T2>::BoundSet::iterator, bool> resultB = mUpperbounds.insert( newBound );
                assert( resultB.second );
                return std::pair<const Bound<T1, T2>*, bool>( *result.first, true );
            }
        }

        template<typename T1, typename T2>
        bool Variable<T1, T2>::deactivateBound( const Bound<T1, T2>* bound, std::list<const smtrat::Formula*>::iterator _position )
        {
            assert( !bound->isInfinite() );
            assert( !bound->isActive() );
            bound->pInfo()->updated = 0;
            bound->pInfo()->position = _position;
            bool variableBoundsChanged = false;
            if( bound->isUpperBound() )
            {
                //check if it is the supremum
                if( mpSupremum == bound )
                {
                    //find the supremum
                    typename Bound<T1, T2>::BoundSet::iterator newBound = mUpperbounds.begin();
                    while( newBound != --mUpperbounds.end() )
                    {
                        if( (*newBound)->isActive() )
                        {
                            ++(*newBound)->pInfo()->updated;
                            break;
                        }
                        ++newBound;
                    }
                    mpSupremum = *newBound;
                    variableBoundsChanged = true;
                }
            }
            if( bound->isLowerBound() )
            {
                //check if it is the infimum
                if( mpInfimum == bound )
                {
                    //find the infimum
                    typename Bound<T1, T2>::BoundSet::reverse_iterator newBound = mLowerbounds.rbegin();
                    while( newBound != --mLowerbounds.rend() )
                    {
                        if( (*newBound)->isActive() )
                        {
                            ++(*newBound)->pInfo()->updated;
                            break;
                        }
                        ++newBound;
                    }
                    mpInfimum = *newBound;
                    variableBoundsChanged = true;
                }
            }
            return variableBoundsChanged;
        }

        template<typename T1, typename T2>
        Interval Variable<T1, T2>::getVariableBounds() const
        {
            carl::BoundType lowerBoundType;
            smtrat::Rational lowerBoundValue;
            carl::BoundType upperBoundType;
            smtrat::Rational upperBoundValue;
            if( infimum().isInfinite() )
            {
                lowerBoundType = carl::BoundType::INFTY;
                lowerBoundValue = 0;
            }
            else
            {
                lowerBoundType = infimum().isWeak() ? carl::BoundType::WEAK : carl::BoundType::STRICT;
                lowerBoundValue = infimum().limit().mainPart();
            }
            if( supremum().isInfinite() )
            {
                upperBoundType = carl::BoundType::INFTY;
                upperBoundValue = 0;
            }
            else
            {
                upperBoundType = supremum().isWeak() ? carl::BoundType::WEAK : carl::BoundType::STRICT;
                upperBoundValue = supremum().limit().mainPart();
            }
            Interval result = Interval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
            return result;
        }

        template<typename T1, typename T2>
        PointerSet<smtrat::Formula> Variable<T1, T2>::getDefiningOrigins() const
        {
            PointerSet<smtrat::Formula> result;
            if( !infimum().isInfinite() )
            {
                result.insert( infimum().origins().front().begin(), infimum().origins().front().end() );
            }
            if( !supremum().isInfinite() )
            {
                result.insert( supremum().origins().front().begin(), supremum().origins().front().end() );
            }
            return result;
        }

        template<typename T1, typename T2>
        void Variable<T1, T2>::print( std::ostream& _out ) const
        {
            std::stringstream out;
            out << *mExpression;
            _out << std::setw( 15 ) << out.str();
            _out << std::setw( 6 ) << "  ->  ";
            _out << std::setw( 35 ) << mAssignment.toString();
            _out << std::setw( 6 ) << "  in [";
            _out << std::setw( 12 ) << mpInfimum->toString();
            _out << std::setw( 2 ) << ", ";
            _out << std::setw( 12 ) << mpSupremum->toString();
            _out << std::setw( 1 ) << "]";
        }

        template<typename T1, typename T2>
        void Variable<T1, T2>::printAllBounds( std::ostream& _out, const std::string _init ) const
        {
            _out << _init << " Upper bounds: " << std::endl;
            for( typename Bound<T1, T2>::BoundSet::const_iterator bIter = mUpperbounds.begin(); bIter != mUpperbounds.end(); ++bIter )
            {
                _out << _init << "     ";
                (*bIter)->print( true, _out, true );
                _out << " [" << (*bIter)->pInfo()->updated << "]" << std::endl;
            }
            _out << _init << " Lower bounds: " << std::endl;
            for( typename Bound<T1, T2>::BoundSet::const_reverse_iterator bIter = mLowerbounds.rbegin(); bIter != mLowerbounds.rend(); ++bIter )
            {
                _out << _init << "     ";
                (*bIter)->print( true, _out, true );
                _out << " [" << (*bIter)->pInfo()->updated << "]" << std::endl;
            }
        }
    }    // end namspace lra
} // end namespace smtrat


