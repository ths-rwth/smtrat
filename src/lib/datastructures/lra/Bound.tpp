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
 * @file Bound.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#pragma once

#include "Bound.h"

namespace smtrat
{
    namespace lra
    {
        template<typename T1, typename T2>
        Bound<T1, T2>::Bound():
            mDeduced( false ),
            mType( UPPER ),
            mLimit( NULL ),
            mVar( NULL ),
            mpAsConstraint( NULL ),
            mpInfo( NULL )
        {
            mpOrigins = new std::vector<PointerSet<Formula> >();
            PointerSet<Formula> originSet = PointerSet<Formula>();
            originSet.insert( NULL );
            mpOrigins->push_back( originSet );
        }

        template<typename T1, typename T2>
        Bound<T1, T2>::Bound( const Value<T1>* const _limit, Variable<T1, T2>* const _var, Type _type, const smtrat::Formula* _constraint, Bound<T1, T2>::Info* _boundInfo, bool _deduced ):
            mDeduced( _deduced ),
            mType( _type ),
            mLimit( _limit ),
            mVar( _var ),
            mpAsConstraint( _constraint ),
            mpInfo( _boundInfo )
        {
            mpOrigins = new std::vector<PointerSet<Formula> >();
            if( _limit == NULL )
            {
                PointerSet<Formula> originSet = PointerSet<Formula>();
                originSet.insert( NULL );
                mpOrigins->push_back( originSet );
            }
        }

        template<typename T1, typename T2>
        Bound<T1, T2>::~Bound()
        {
            delete mpInfo;
            delete mpOrigins;
            delete mLimit;
        }

        template<typename T1, typename T2>
        bool Bound<T1, T2>::operator <( const Bound& _bound ) const
        {
            assert( mType == EQUAL || _bound.type() == EQUAL || mType == _bound.type() );
            if( mLimit == NULL && _bound.pLimit() == NULL )
            {
                return false;
            }
            else if( mLimit == NULL && _bound.pLimit() != NULL )
            {
                return mType == LOWER;
            }
            else if( mLimit != NULL && _bound.pLimit() == NULL )
            {
                return _bound.type() == UPPER;
            }
            else
            {
                if( (*mLimit) < _bound.limit() )
                {
                    return true;
                }
                else if( (*mLimit) == _bound.limit() )
                {
                    if( mType == LOWER && _bound.type() == EQUAL ) return true;
                    if( mType == EQUAL && _bound.type() == UPPER ) return true;
                }
                return false;
            }
        }

        template<typename T1, typename T2>
        bool Bound<T1, T2>::operator >( const Bound& _bound ) const
        {
            if( mLimit == NULL && _bound.pLimit() == NULL )
            {
                return (mType == UPPER && _bound.type() == LOWER);
            }
            else if( mLimit == NULL && _bound.pLimit() != NULL )
            {
                return mType == UPPER;
            }
            else if( mLimit != NULL && _bound.pLimit() == NULL )
            {
                return _bound.type() == LOWER;
            }
            else
            {
                if( (*mLimit) > _bound.limit() )
                {
                    return true;
                }
                else if( (*mLimit) == _bound.limit() )
                {
                    if( mType != EQUAL && _bound.type() == EQUAL ) return true;
                }
                return false;
            }
        }

        template<typename T1, typename T2>
        bool Bound<T1, T2>::operator <( const Value<T1>& _value ) const
        {
            if( mLimit == NULL && mType == UPPER )
            {
                return false;
            }
            else if( mLimit == NULL && mType == LOWER )
            {
                return true;
            }
            else
            {
                return (*mLimit) < _value;
            }
        }

        template<typename T1, typename T2>
        bool Bound<T1, T2>::operator >( const Value<T1>& _value ) const
        {
            if( mLimit == NULL && mType == UPPER )
            {
                return true;
            }
            else if( mLimit == NULL && mType == LOWER )
            {
                return false;
            }
            else
            {
                return (*mLimit) > _value;
            }
        }

        template<typename T1, typename T2>
        bool Bound<T1, T2>::operator ==( const Value<T1>& _value ) const
        {
            if( mLimit == NULL )
            {
                return false;
            }
            return (*mLimit) == _value;
        }
        
        template<typename T1, typename T2>
        bool Bound<T1, T2>::operator ==( const T1& _a ) const
        {
            return mLimit != NULL && (*mLimit) == _a;
        }
        
        template<typename T1, typename T2>
        bool Bound<T1, T2>::operator >( const T1& _a ) const
        {
            if( mLimit == NULL )
                return mType == UPPER;
            return (*mLimit) > _a;
        }
        
        template<typename T1, typename T2>
        bool Bound<T1, T2>::operator <( const T1& _a ) const
        {
            if( mLimit == NULL )
                return mType == LOWER;
            return (*mLimit) < _a;
        }
        
        template<typename T1, typename T2>
        bool Bound<T1, T2>::operator >=( const T1& _a ) const
        {
            if( mLimit == NULL )
                return mType == UPPER;
            return (*mLimit) >= _a;
        }
        
        template<typename T1, typename T2>
        bool Bound<T1, T2>::operator <=( const T1& _a ) const
        {
            if( mLimit == NULL )
                return mType == LOWER;
            return (*mLimit) <= _a;
        }

        template<typename T1, typename T2>
        const std::string Bound<T1, T2>::toString() const
        {
            if( mLimit == NULL && mType == UPPER )
            {
                return "oo";
            }
            else if( mLimit == NULL && mType == LOWER )
            {
                return "-oo";
            }
            else
            {
                return limit().toString();
            }
        }

        template<typename T3, typename T4>
        std::ostream& operator <<( std::ostream& _ostream, const Bound<T3, T4>& _bound )
        {
            _bound.print( false, _ostream, false );
            return _ostream;
        }

        template<typename T1, typename T2>
        void Bound<T1, T2>::print( bool _withOrigins, std::ostream& _out, bool _printType ) const
        {
            if( _printType )
            {
                if( mType == UPPER )
                {
                    _out << "<=";
                }
                else if( mType == LOWER )
                {
                    _out << ">=";
                }
                else
                {
                    _out << "==";
                }
            }
            if( mLimit == NULL && mType == UPPER )
            {
                _out << "inf";
            }
            else if( mLimit == NULL && mType == LOWER )
            {
                _out << "-inf";
            }
            else
            {
                limit().print();
                if( _withOrigins && mpAsConstraint != NULL )
                    _out << "  from  " << *mpAsConstraint;
                if( _withOrigins && mpInfo->neqRepresentation != NULL )
                    _out << " [" << *mpInfo->neqRepresentation << "]";
            }
            if( mDeduced ) _out << " (deduced) ";
            if( _withOrigins )
            {
                _out << "  ( ";
                for( auto originSet = origins().begin(); originSet != origins().end(); ++originSet )
                {
                    _out << "{ ";
                    for( auto origin = originSet->begin(); origin != originSet->end(); ++origin )
                    {
                        if( *origin != NULL )
                        {
                            _out << **origin << " ";
                        }
                        else
                        {
                            _out << "NULL ";
                        }
                    }
                    _out << "} ";
                }
                _out << ")";
            }
        }

    }    // end namspace lra
}    // end namspace smtrat
