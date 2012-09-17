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
        mBasic( true ),
        mPosition( 0 ),
        mUpperbounds( BoundSet() ),
        mLowerbounds( BoundSet() ),
        mAssignment()
    {
        mpSupremum = addUpperBound( NULL ).first;
        mpInfimum  = addLowerBound( NULL ).first;
    }

    Variable::Variable( unsigned _position, bool _basic, const ex* _expression ):
        mBasic( _basic ),
        mPosition( _position ),
        mUpperbounds( BoundSet() ),
        mLowerbounds( BoundSet() ),
        mExpression( _expression),
        mAssignment()
    {
        mpSupremum = addUpperBound( NULL ).first;
        mpInfimum  = addLowerBound( NULL ).first;
    }

    Variable::~Variable()
    {
        while( !mLowerbounds.empty() )
        {
            const Bound* b = *mLowerbounds.begin();
            mLowerbounds.erase( mLowerbounds.begin() );
            delete b;
        }
        while( !mUpperbounds.empty() )
        {
            const Bound* b = *mUpperbounds.begin();
            mUpperbounds.erase( mUpperbounds.begin() );
            delete b;
        }
    }

    /**
     *
     * @param _val
     * @return
     */
    pair<const Bound*,pair<const Bound*, const Bound*> > Variable::addLowerBound( Value* const _val, const smtrat::Constraint* _constraint )
    {
        const Bound*                 newBound = new Bound( _val, this, false, _constraint );
        pair<BoundSet::iterator, bool> result = mLowerbounds.insert( newBound );
        if( !result.second )
        {
            delete newBound;
            return pair<const Bound*,pair<const Bound*, const Bound*> >( *result.first, pair<const Bound*, const Bound*>( NULL, NULL ) );
        }
        else
        {
            const Bound* nextStrongerBound = NULL;
            const Bound* nextWeakerBound = NULL;
            ++result.first;
            if( result.first != mLowerbounds.end() )
            {
                nextStrongerBound = *result.first;
            }
            --result.first;
            if( result.first != mLowerbounds.begin() )
            {
                --result.first;
                nextWeakerBound = *result.first;
                ++result.first;
            }
            return pair<const Bound*,pair<const Bound*, const Bound*> >( *result.first, pair<const Bound*, const Bound*>( nextStrongerBound, nextWeakerBound ) );
        }
    }

    /**
     *
     * @param _val
     * @return
     */
    pair<const Bound*,pair<const Bound*, const Bound*> > Variable::addUpperBound( Value* const _val, const smtrat::Constraint* _constraint )
    {
        const Bound*                 newBound = new Bound( _val, this, true, _constraint );
        pair<BoundSet::iterator, bool> result = mUpperbounds.insert( newBound );
        if( !result.second )
        {
            delete newBound;
            return pair<const Bound*,pair<const Bound*, const Bound*> >( *result.first, pair<const Bound*, const Bound*>( NULL, NULL ) );
        }
        else
        {
            const Bound* nextStrongerBound = NULL;
            const Bound* nextWeakerBound = NULL;
            if( result.first != mUpperbounds.begin() )
            {
                nextStrongerBound = *(--result.first);
                ++result.first;
            }
            if( result.first != mUpperbounds.end() )
            {
                if( ++result.first != mUpperbounds.end() )
                {
                    nextWeakerBound = *result.first;
                }
                --result.first;
            }
            return pair<const Bound*,pair<const Bound*, const Bound*> >( *result.first, pair<const Bound*, const Bound*>( nextStrongerBound, nextWeakerBound ) );
        }
    }

    /**
     *
     * @param bound
     */
    void Variable::deactivateBound( const Bound* bound )
    {
        if( bound->isUpper() )
        {
            //check if it is the supremum
            if( mpSupremum == bound )
            {
                //find the supremum
                BoundSet::iterator newBound = mUpperbounds.begin();
                while( newBound != mUpperbounds.end() )
                {
                    if( (*newBound)->isActive() )
                    {
                        mpSupremum = *newBound;
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
            if( mpInfimum == bound )
            {
                //find the infimum
                BoundSet::reverse_iterator newBound = mLowerbounds.rbegin();
                while( newBound != mLowerbounds.rend() )
                {
                    if( (*newBound)->isActive() )
                    {
                        mpInfimum = *newBound;
                        break;
                    }
                    ++newBound;
                }
                assert( newBound != mLowerbounds.rend() );
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

    void Variable::printAllBounds( std::ostream& _out, const std::string _init ) const
    {
        _out << _init << " Upper bounds: " << endl;
        for( BoundSet::const_iterator bIter = mUpperbounds.begin(); bIter != mUpperbounds.end(); ++bIter )
        {
            _out << _init << "     ";
            (*bIter)->print( _out, true, true );
            _out << endl;
        }
        _out << _init << " Lower bounds: " << endl;
        for( BoundSet::const_iterator bIter = mLowerbounds.begin(); bIter != mLowerbounds.end(); ++bIter )
        {
            _out << _init << "     ";
            (*bIter)->print( _out, true, true );
            _out << endl;
        }
    }
}    // end namspace lra

