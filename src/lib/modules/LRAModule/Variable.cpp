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

namespace lra
{
    Variable::Variable( unsigned _position, bool _basic, const ex* _expression, smtrat::Formula::iterator _defaultBoundPosition ):
        mBasic( _basic ),
        mPosition( _position ),
        mUpperbounds( BoundSet() ),
        mLowerbounds( BoundSet() ),
        mExpression( _expression),
        mAssignment()
    {
        mpSupremum = addUpperBound( NULL, _defaultBoundPosition ).first;
        mpInfimum  = addLowerBound( NULL, _defaultBoundPosition ).first;
    }

    Variable::~Variable()
    {
        while( !mLowerbounds.empty() )
        {
            const Bound* b = *mLowerbounds.begin();
            mLowerbounds.erase( mLowerbounds.begin() );
            if( !b->type() == Bound::EQUAL ) delete b;
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
    pair<const Bound*,pair<const Bound*, const Bound*> > Variable::addUpperBound( Value* const _val, smtrat::Formula::iterator _position, const smtrat::Constraint* _constraint, bool _deduced )
    {
        Bound::Info* boundInfo = new Bound::Info();
        boundInfo->updated = 0;
        boundInfo->position = _position;
        const Bound* newBound = new Bound( _val, this, Bound::UPPER, _constraint, boundInfo, _deduced );
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
                ++result.first;
                while( result.first != mUpperbounds.end() )
                {
                    if( (*result.first)->type() != Bound::EQUAL )
                    {
                        nextWeakerBound = *result.first;
                        break;
                    }
                    ++result.first;
                }
            }
            return pair<const Bound*,pair<const Bound*, const Bound*> >( newBound, pair<const Bound*, const Bound*>( nextStrongerBound, nextWeakerBound ) );
        }
    }

    /**
     *
     * @param _val
     * @return
     */
    pair<const Bound*,pair<const Bound*, const Bound*> > Variable::addLowerBound( Value* const _val, smtrat::Formula::iterator _position, const smtrat::Constraint* _constraint, bool _deduced )
    {
        Bound::Info* boundInfo = new Bound::Info();
        boundInfo->updated = 0;
        boundInfo->position = _position;
        const Bound* newBound = new Bound( _val, this, Bound::LOWER, _constraint, boundInfo, _deduced );
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
            while( result.first != mLowerbounds.begin() )
            {
                --result.first;
                if( (*result.first)->type() != Bound::EQUAL )
                {
                    nextWeakerBound = *result.first;
                    break;
                }
            }
            return pair<const Bound*,pair<const Bound*, const Bound*> >( newBound, pair<const Bound*, const Bound*>( nextStrongerBound, nextWeakerBound ) );
        }
    }

    /**
     *
     * @param _val
     * @return
     */
    pair<const Bound*,pair<const Bound*, const Bound*> > Variable::addEqualBound( Value* const _val, smtrat::Formula::iterator _position, const smtrat::Constraint* _constraint )
    {
        Bound::Info* boundInfo = new Bound::Info();
        boundInfo->updated = 0;
        boundInfo->position = _position;
        const Bound* newBound = new Bound( _val, this, Bound::EQUAL, _constraint, boundInfo );
        pair<BoundSet::iterator, bool> result = mLowerbounds.insert( newBound );
        if( !result.second )
        {
            delete newBound;
            return pair<const Bound*,pair<const Bound*, const Bound*> >( *result.first, pair<const Bound*, const Bound*>( NULL, NULL ) );
        }
        else
        {
            const Bound* nextWeakerLowerBound = NULL;
            while( result.first != mLowerbounds.begin() )
            {
                --result.first;
                if( (*result.first)->type() != Bound::EQUAL )
                {
                    nextWeakerLowerBound = *result.first;
                    break;
                }
            }
            pair<BoundSet::iterator, bool> result = mUpperbounds.insert( newBound );
            ++result.first;
            const Bound* nextWeakerUpperBound = NULL;
            while( result.first != mUpperbounds.end() )
            {
                if( (*result.first)->type() != Bound::EQUAL )
                {
                    nextWeakerUpperBound = *result.first;
                    break;
                }
                ++result.first;
            }
            return pair<const Bound*,pair<const Bound*, const Bound*> >( newBound, pair<const Bound*, const Bound*>( nextWeakerLowerBound, nextWeakerUpperBound ) );
        }
    }

    /**
     *
     * @param bound
     */
    void Variable::deactivateBound( const Bound* bound, smtrat::Formula::iterator _position )
    {
        assert( !bound->isInfinite() );
        assert( !bound->isActive() );
        bound->pInfo()->updated = 0;
        bound->pInfo()->position = _position;
        if( bound->isUpperBound() )
        {
            //check if it is the supremum
            if( mpSupremum == bound )
            {
                //find the supremum
                BoundSet::iterator newBound = mUpperbounds.begin();
                while( newBound != --mUpperbounds.end() )
                {
                    if( (*newBound)->isActive() )
                    {
                        ++(*newBound)->pInfo()->updated;
                        mpSupremum = *newBound;
                        goto LowerBounds;
                    }
                    ++newBound;
                }
                mpSupremum = *newBound;
            }
        }
LowerBounds:
        if( bound->isLowerBound() )
        {
            //check if it is the infimum
            if( mpInfimum == bound )
            {
                //find the infimum
                BoundSet::reverse_iterator newBound = mLowerbounds.rbegin();
                while( newBound != --mLowerbounds.rend() )
                {
                    if( (*newBound)->isActive() )
                    {
                        ++(*newBound)->pInfo()->updated;
                        mpInfimum = *newBound;
                        return;
                    }
                    ++newBound;
                }
                mpInfimum = *newBound;
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
            (*bIter)->print( true, _out, true );
            _out << " [" << (*bIter)->pInfo()->updated << "]" << endl;
        }
        _out << _init << " Lower bounds: " << endl;
        for( BoundSet::const_reverse_iterator bIter = mLowerbounds.rbegin(); bIter != mLowerbounds.rend(); ++bIter )
        {
            _out << _init << "     ";
            (*bIter)->print( true, _out, true );
            _out << " [" << (*bIter)->pInfo()->updated << "]" << endl;
        }
    }
}    // end namspace lra

