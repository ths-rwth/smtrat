/*
 * File:   Variable.cpp
 * Author: x
 *
 * Created on April 30, 2012, 5:47 PM
 */

#include "Variable.h"

using namespace std;

namespace lraone
{
    Variable::Variable():
        mAssignment(),
        mPriority( 0 ),
        mBasic( true ),
        mPosition( 0 ),
        mUBs( new boundActivityMap() ),
        mLBs( new boundActivityMap() )
    {
        mSupremum = addUpperBound( NULL );
        mInfimum  = addLowerBound( NULL );
    }

    Variable::Variable( int _priority, unsigned _position, bool _basic ):
        mAssignment(),
        mPriority( _priority ),
        mBasic( _basic ),
        mPosition( _position ),
        mUBs( new boundActivityMap() ),
        mLBs( new boundActivityMap() )
    {
        mSupremum = addUpperBound( NULL );
        mInfimum  = addLowerBound( NULL );
    }

    Variable::~Variable()
    {
        while( !mLBs->empty() )
        {
            const Bound* b = mLBs->begin()->first;
            mLBs->erase( mLBs->begin() );
            delete b;
        }
        while( !mUBs->empty() )
        {
            const Bound* b = mUBs->begin()->first;
            mUBs->erase( mUBs->begin() );
            delete b;
        }
    }

    /**
     *
     * @param _val
     * @return
     */
    const Bound* Variable::addLowerBound( Value* const _val )
    {
        const Bound*                           b = new Bound( _val, this, false );
        pair<boundActivityMap::iterator, bool> p = mLBs->insert( pair<const Bound*, bool>( b, _val == NULL ) );
        if( !p.second )
        {
            delete b;
        }
        return p.first->first;
    }

    /**
     *
     * @param _val
     * @return
     */
    const Bound* Variable::addUpperBound( Value* const _val )
    {
        const Bound*                           b = new Bound( _val, this, true );
        pair<boundActivityMap::iterator, bool> p = mUBs->insert( pair<const Bound*, bool>( b, _val == NULL ) );
        if( !p.second )
        {
            delete b;
        }
        return p.first->first;
    }

    /**
     *
     * @param _out
     */
    void Variable::print( std::ostream& _out ) const
    {
        _out << " Variable " << this << endl;
        _out << "   Priority: " << mPriority << endl;
        _out << "   Position: " << mPosition << endl;
        _out << "   Is a basic: " << ( mBasic ? "yes" : "no" ) << endl;
        _out << "   Assignment: ";
        mAssignment.print();
        _out << endl;
        _out << "   Upper bounds: " << endl;
        for( boundActivityMap::const_iterator bIter = mUBs->begin(); bIter != mUBs->end(); ++bIter )
        {
            _out << "     ";
            (*bIter).first->print();
            _out << endl;
        }
        _out << "   Lower bounds: " << endl;
        for( boundActivityMap::const_iterator bIter = mLBs->begin(); bIter != mLBs->end(); ++bIter )
        {
            _out << "     ";
            (*bIter).first->print();
            _out << endl;
        }
    }
}    // end namspace lra

