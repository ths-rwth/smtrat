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


/*
 * File:   variable.h
 * Author: Stefan Schupp
 *
 * Created on January 15, 2013, 10:40 AM
 */

#ifndef VARIABLE_H
#define VARIABLE_H

#include "ContractionCandidate.h"
#include "../../Formula.h"
#include <assert.h>

namespace smtrat
{
namespace icp
{
    class IcpVariable
    {
        private:

            /*
             * Members
             */
            GiNaC::symbol                              mVar;
            bool                                       mOriginal;
            std::vector<ContractionCandidate*> mCandidates;
            lra::Variable*                             mLraVar;
            GiNaCRA::evaldoubleintervalmap::iterator    mInterval;
            bool                                       mActive;
            bool                                       mLinear;
            
            // interval Bound generation
            bool                                       mBoundsSet; // indicates if bounds have already been set -> only update them, else create new formula in passed Formula
            bool                                       mUpdated;
            smtrat::Formula::iterator                  mLeftBound;
            smtrat::Formula::iterator                  mRightBound;

        public:

            /*
             * Constructors
             */

            IcpVariable():
            mOriginal(false)
            {}

            IcpVariable( symbol _var, bool _original, GiNaCRA::evaldoubleintervalmap::iterator _interval, lra::Variable* _lraVar = NULL ):
                mVar( _var ),
                mOriginal( _original ),
                mCandidates(),
                mLraVar( _lraVar ),
                mInterval( _interval ),
                mActive( false ),
                mLinear( true ),
                mBoundsSet( false ),
                mUpdated( false ),
                mLeftBound ( ),
                mRightBound ( )
            {
                assert( (*_interval).first == mVar );
            }

            IcpVariable( symbol _var,
                         bool _original,
                         ContractionCandidate* _candidate,
                         GiNaCRA::evaldoubleintervalmap::iterator _interval,
                         lra::Variable* _lraVar = NULL ):
                mVar( _var ),
                mOriginal ( _original ),
                mCandidates(),
                mLraVar( _lraVar ),
                mInterval( _interval ),
                mActive( _candidate->isActive() ),
                mLinear( _candidate->isLinear() ),
                mBoundsSet (false),
                mUpdated( false ),
                mLeftBound ( ),
                mRightBound ( )
            {
                assert( (*_interval).first == mVar );
                addCandidate( _candidate );
            }

            /*
             * Getter/Setter
             */

            const GiNaC::symbol var() const
            {
                return mVar;
            }

            std::vector<ContractionCandidate*>& candidates()
            {
                return mCandidates;
            }

            const lra::Variable* lraVar() const
            {
                return mLraVar;
            }

            const GiNaCRA::evaldoubleintervalmap::iterator interval() const
            {
                return mInterval;
            }

            void addCandidate( ContractionCandidate* _candidate )
            {
                mCandidates.insert( mCandidates.end(), _candidate );
                if( _candidate->isActive() )
                {
                    mActive = true;
                }
            }

            void updateInterval( GiNaCRA::DoubleInterval _interval )
            {
                mUpdated = true;
                (*mInterval).second = _interval;
            }

            void setLraVar( lra::Variable* _lraVar )
            {
                mLraVar = _lraVar;
            }

            void deleteCandidate( ContractionCandidate* _candidate )
            {
                std::vector<ContractionCandidate*>::iterator candidateIt;
                for( candidateIt = mCandidates.begin(); candidateIt != mCandidates.end(); ++candidateIt )
                {
                    if( *candidateIt == _candidate )
                    {
                        mCandidates.erase( candidateIt );
                    }
                }
            }

            void print( ostream& _out = std::cout ) const
            {
                _out << mVar << ", ";
                if( mLraVar != NULL )
                {
                    mLraVar->print();
                }
                _out << "\t ";
                (*mInterval).second.dbgprint();
                if ( (*mInterval).second.unbounded() )
                {
                    _out << endl;
                }
            }

            bool isActive() const
            {
                return mActive;
            }

            void activate()
            {
                mActive = true;
            }

            void deactivate()
            {
                mActive = false;
            }

            bool checkLinear()
            {
                std::vector<ContractionCandidate*>::iterator candidateIt = mCandidates.begin();
                for ( ; candidateIt != mCandidates.end(); ++candidateIt )
                {
                    if ( (*candidateIt)->isLinear() == false )
                    {
                        mLinear = false;
                        return false;
                    }
                }
                mLinear = true;
                return true;
            }
            
            bool isLinear()
            {
                return mLinear;
            }
            
            void setUpdated(bool _updated=true)
            {
                mUpdated = _updated;
            }
            
            bool isUpdated() const
            {
                return mUpdated;
            }
            
            smtrat::Formula::iterator leftBound() const
            {
                assert(mBoundsSet);
                return mLeftBound;
            }
            
            smtrat::Formula::iterator rightBound() const
            {
                assert(mBoundsSet);
                return mRightBound;
            }
            
            void setLeftBound( smtrat::Formula::iterator _left )
            {
                mLeftBound = _left;
            }
            
            void setRightBound( smtrat::Formula::iterator _right )
            {
                mRightBound = _right;
            }
            
            void boundsSet()
            {
                mBoundsSet = true;
            }
            
            bool isBoundsSet()
            {
                return mBoundsSet;
            }
            
            const bool isOriginal() const
            {
                return mOriginal;
            }
            
            /**
             * Checks all candidates if at least one is active - if so, set variable as active.
             * @return true if variable is active
             */
            bool autoActivate()
            {
                std::vector<ContractionCandidate*>::iterator candidateIt;
                for( candidateIt = mCandidates.begin(); candidateIt != mCandidates.end(); ++candidateIt )
                {
                    if( (*candidateIt)->isActive() )
                    {
                        mActive = true;
                        return mActive;
                    }
                }
                return false;
            }

        private:

            /*
             * Auxiliary functions
             */
    };
}    // namespace icp
} // namespace smtrat
#endif   /* VARIABLE_H */
