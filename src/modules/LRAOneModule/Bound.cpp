/*
 * File:   Bound.cpp
 * Author: x
 *
 * Created on April 30, 2012, 6:19 PM
 */

#include "Bound.h"

using namespace std;

namespace lraone
{
    Bound::Bound():
        mLimit( NULL ),
        mIsUpper( true ),
        mVar( NULL )
    {}

    Bound::Bound( Value* const _limit, Variable* const _var, bool _isUpper ):
        mLimit( _limit ),
        mIsUpper( _isUpper ),
        mVar( _var )
    {}

    Bound::~Bound(){}

    /**
     *
     * @param _bound
     * @return
     */
    bool Bound::operator <( const Bound& _bound ) const
    {
        assert( (this->mIsUpper && _bound.getIsUpper()) || (!this->mIsUpper &&!_bound.getIsUpper()) );
        if( mLimit == NULL && _bound.pLimit() != NULL )
        {
            if( this->mIsUpper )
            {
                return false;
            }
            else
            {
                return true;
            }
        }
        else if( mLimit != NULL && _bound.pLimit() == NULL )
        {
            if( _bound.mIsUpper )
            {
                return true;
            }
            else
            {
                return false;
            }
        }
        else
        {
            return (*mLimit) < _bound.limit();
        }
    }

    /**
     *
     * @param _bound
     * @return
     */
    bool Bound::operator >( const Bound& _bound ) const
    {
        if( mLimit == NULL && _bound.pLimit() != NULL )
        {
            if( this->mIsUpper )
            {
                return true;
            }
            else
            {
                return false;
            }
        }
        else if( mLimit != NULL && _bound.pLimit() == NULL )
        {
            if( _bound.mIsUpper )
            {
                return false;
            }
            else
            {
                return true;
            }
        }
        else if( mLimit == NULL && _bound.pLimit() == NULL )
        {
            assert( (_bound.mIsUpper && mIsUpper) || (!_bound.mIsUpper &&!mIsUpper) );
            return false;
        }
        else
        {
            return (*mLimit) > _bound.limit();
        }
    }

    /**
     *
     * @param v
     * @return
     */
    bool Bound::operator <( const Value& v ) const
    {
        if( mLimit == NULL && mIsUpper )
        {
            return false;
        }
        else if( mLimit == NULL &&!mIsUpper )
        {
            return true;
        }
        else
        {
            return (*mLimit) < v;
        }
    }

    /**
     *
     * @param v
     * @return
     */
    bool Bound::operator >( const Value& v ) const
    {
        if( mLimit == NULL && mIsUpper )
        {
            return true;
        }
        else if( mLimit == NULL &&!mIsUpper )
        {
            return false;
        }
        else
        {
            return (*mLimit) > v;
        }
    }

    /**
     *
     * @param v
     * @return
     */
    bool Bound::operator ==( const Value& v ) const
    {
        if( mLimit == NULL )
        {
            return false;
        }
        return (*mLimit) == v;
    }

    /**
     *
     * @param _out
     */
    void Bound::print( std::ostream& _out ) const
    {
        if( mIsUpper )
        {
            _out << "UpperBound = ";
        }
        else
        {
            _out << "LowerBound = ";
        }

        if( this->mLimit == NULL && mIsUpper )
        {
            _out << "infinity";
        }
        else if( this->mLimit == NULL &&!mIsUpper )
        {
            _out << "- infinity";
        }
        else
        {
            limit().print();
        }
    }

}    // end namspace lra

