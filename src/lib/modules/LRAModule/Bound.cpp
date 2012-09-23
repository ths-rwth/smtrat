/*
 * File:   Bound.cpp
 * Author: x
 *
 * Created on April 30, 2012, 6:19 PM
 */

#include "Bound.h"

using namespace std;

namespace lra
{
    Bound::Bound():
        mLimit( NULL ),
        mIsUpper( true ),
        mVar( NULL ),
        mpAsConstraint( NULL )
    {
        mpOrigins = new vector<set< const smtrat::Formula* > >();
        set< const smtrat::Formula* > originSet = set< const smtrat::Formula* >();
        originSet.insert( NULL );
        mpOrigins->push_back( originSet );
    }

    Bound::Bound( Value* const _limit, Variable* const _var, bool _isUpper, const smtrat::Constraint* _constraint ):
        mLimit( _limit ),
        mIsUpper( _isUpper ),
        mVar( _var ),
        mpAsConstraint( _constraint )
    {
        mpOrigins = new vector<set< const smtrat::Formula* > >();
        if( _limit == NULL )
        {
            set< const smtrat::Formula* > originSet = set< const smtrat::Formula* >();
            originSet.insert( NULL );
            mpOrigins->push_back( originSet );
        }
    }

    Bound::~Bound()
    {
        delete mpOrigins;
        delete mLimit;
    }

    /**
     *
     * @param _bound
     * @return
     */
    bool Bound::operator <( const Bound& _bound ) const
    {
        if( mLimit == NULL && _bound.pLimit() == NULL )
        {
            return (!mIsUpper && _bound.isUpper());
        }
        else if( mLimit == NULL && _bound.pLimit() != NULL )
        {
            if( mIsUpper )
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
        if( mLimit == NULL && _bound.pLimit() == NULL )
        {
            return (mIsUpper && !_bound.isUpper());
        }
        else if( mLimit == NULL && _bound.pLimit() != NULL )
        {
            if( mIsUpper )
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
     * @return
     */
    const string Bound::toString() const
    {
        if( mLimit == NULL && mIsUpper )
        {
            return "inf";
        }
        else if( mLimit == NULL &&!mIsUpper )
        {
            return "-inf";
        }
        else
        {
            return limit().toString();
        }
    }

    /**
     *
     * @param _ostream
     * @param _bound
     * @return
     */
    ostream& operator <<( ostream& _ostream, const Bound& _bound )
    {
        _bound.print( _ostream, false );
        return _ostream;
    }

    /**
     *
     * @param _out
     */
    void Bound::print( std::ostream& _out, bool _printType, bool _withOrigins ) const
    {
        if( _printType )
        {
            if( mIsUpper )
            {
                _out << "<";
            }
            else
            {
                _out << ">";
            }
        }
        if( mLimit == NULL && mIsUpper )
        {
            _out << "inf";
        }
        else if( mLimit == NULL &&!mIsUpper )
        {
            _out << "-inf";
        }
        else
        {
            limit().print();
            assert( mpAsConstraint != NULL );
            _out << "  from  " << *mpAsConstraint;
        }
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

