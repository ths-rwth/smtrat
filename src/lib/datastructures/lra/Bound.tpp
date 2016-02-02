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
#ifdef __VS
            Bound<T1, T2>::Bound(const Value<T1>* const _limit, Variable<T1, T2>* const _var, Type _type, const FormulaT& _constraint, Info* _boundInfo, bool _deduced) :
#else
            Bound<T1, T2>::Bound(const Value<T1>* const _limit, Variable<T1, T2>* const _var, Type _type, const FormulaT& _constraint, Bound<T1, T2>::Info* _boundInfo, bool _deduced) :
#endif
            mDeduced( _deduced ),
            mMarkedAsDeleted( false ),
            mType( _type ),
            mLimit( _limit ),
            mVar( _var ),
            mAsConstraint( _constraint ),
            mpInfo( _boundInfo )
        {
            mpOrigins = std::shared_ptr<std::vector<FormulaT>>(new std::vector<FormulaT>());
            if( _limit == NULL )
            {
                mpOrigins->push_back( FormulaT( carl::FormulaType::TRUE ) );
            }
        }

        template<typename T1, typename T2>
        Bound<T1, T2>::~Bound()
        {
            delete mpInfo;
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
                if( _withOrigins )
                    _out << "  from  " << mAsConstraint;
                if( _withOrigins )
                    _out << " [" << mpInfo->neqRepresentation << "]";
            }
            if( mDeduced ) _out << " (deduced) ";
            if( _withOrigins )
            {
                _out << "  ( ";
                for( auto origin = origins().begin(); origin != origins().end(); ++origin )
                {
                    _out << *origin << " ";
                }
                _out << ")";
            }
        }

    }    // end namspace lra
}    // end namspace smtrat
