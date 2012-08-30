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
 * @file Variable.cpp
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#include <sstream>

#include "Variable.h"

using namespace std;
using namespace GiNaC;

namespace lraone
{
    Variable::Variable():
        mAssignment(),
        mBasic( true ),
        mPosition( 0 ),
        mUpperbounds( BoundActivityMap() ),
        mLowerbounds( BoundActivityMap() )
    {
        mpSupremum = addUpperBound( NULL );
        mpInfimum  = addLowerBound( NULL );
    }

    Variable::Variable( unsigned _position, bool _basic, const ex* _expression ):
        mAssignment(),
        mBasic( _basic ),
        mPosition( _position ),
        mUpperbounds( BoundActivityMap() ),
        mLowerbounds( BoundActivityMap() ),
        mExpression( _expression)
    {
        mpSupremum = addUpperBound( NULL );
        mpInfimum  = addLowerBound( NULL );
    }

    Variable::~Variable()
    {
        while( !mLowerbounds.empty() )
        {
            const Bound* b = mLowerbounds.begin()->first;
            mLowerbounds.erase( mLowerbounds.begin() );
            delete b;
        }
        while( !mUpperbounds.empty() )
        {
            const Bound* b = mUpperbounds.begin()->first;
            mUpperbounds.erase( mUpperbounds.begin() );
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
        pair<BoundActivityMap::iterator, bool> p = mLowerbounds.insert( pair<const Bound*, bool>( b, _val == NULL ) );
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
        pair<BoundActivityMap::iterator, bool> p = mUpperbounds.insert( pair<const Bound*, bool>( b, _val == NULL ) );
        if( !p.second )
        {
            delete b;
        }
        return p.first->first;
    }

    /**
     *
     * @param _bound
     * @param _active
     * @return
     */
    unsigned Variable::setActive( const Bound* _bound, bool _active )
    {
        assert( _bound != NULL );
        if( _bound->isUpper() )
        {
            BoundActivityMap::iterator iter = mUpperbounds.find( _bound );
            assert( iter != mUpperbounds.end() );
            if( _active )
            {
                return ++iter->second;
            }
            else
            {
                assert( iter->second > 0 );
                return --iter->second;
            }
        }
        else
        {
            BoundActivityMap::iterator iter = mLowerbounds.find( _bound );
            assert( iter != mLowerbounds.end() );
            if( _active )
            {
                return ++iter->second;
            }
            else
            {
                assert( iter->second > 0 );
                return --iter->second;
            }
        }
    }

    /**
     *
     * @param bound
     */
    void Variable::deactivateBound( const Bound* bound )
    {
        // Bound gets deactivated
        if( setActive( bound, false ) == 0 )
        {
            if( bound->isUpper() )
            {
                //check if it is the supremum
                if( pSupremum() == bound )
                {
                    //find the supremum
                    BoundActivityMap::iterator newBound = mUpperbounds.begin();
                    while( newBound != mUpperbounds.end() )
                    {
                        if( newBound->second > 0 )
                        {
                            setSupremum( newBound->first );
                            break;
                        }
                        ++newBound;
                    }
                    assert( newBound != mUpperbounds.end() );
                }
            }
            else
            {
                //check if it is the infimum
                if( pInfimum() == bound )
                {
                    //find the infimum
                    BoundActivityMap::iterator newBound = mLowerbounds.begin();
                    while( newBound != mLowerbounds.end() )
                    {
                        if( newBound->second > 0 )
                        {
                            setInfimum( newBound->first );
                            break;
                        }
                        ++newBound;
                    }
                    assert( newBound != mLowerbounds.end() );
                }
            }
        }
    }

    /**
     *
     * @param _out
     */
    void Variable::print( std::ostream& _out ) const
    {
        stringstream out;
        out << *mExpression;
        _out << setw( 15 ) << out.str();
        _out << setw( 6 ) << "  ->  ";
        _out << setw( 35 ) << mAssignment.toString();
        _out << setw( 6 ) << "  in [";
        _out << setw( 12 ) << mpInfimum->toString();
        _out << setw( 2 ) << ", ";
        _out << setw( 12 ) << mpSupremum->toString();
        _out << setw( 1 ) << "]";
    }

    void Variable::printAllBounds( std::ostream& _out ) const
    {
        _out << " Upper bounds: " << endl;
        for( BoundActivityMap::const_iterator bIter = mUpperbounds.begin(); bIter != mUpperbounds.end(); ++bIter )
        {
            _out << "  ";
            (*bIter).first->print( _out, true );
            _out << endl;
        }
        _out << " Lower bounds: " << endl;
        for( BoundActivityMap::const_iterator bIter = mLowerbounds.begin(); bIter != mLowerbounds.end(); ++bIter )
        {
            _out << "  ";
            (*bIter).first->print( _out, true );
            _out << endl;
        }
    }
}    // end namspace lra

