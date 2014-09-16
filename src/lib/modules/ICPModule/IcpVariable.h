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
#include "../LRAModule/LRAModule.h"
#include <assert.h>

namespace smtrat
{
    
    typedef std::set<icp::ContractionCandidate*, icp::contractionCandidateComp> ContractionCandidates;
    
namespace icp
{   
    enum class Updated{
        // leftBound was updated
        LEFT,
        // rightBound was updated
        RIGHT,
        // both Bounds were updated
        BOTH,
        // no bound was updated
        NONE
    };
    
    class IcpVariable
    {
        private:

            /*
             * Members
             */
            carl::Variable               mVar;
            bool                               mOriginal;
            ContractionCandidates              mCandidates;
            const LRAVariable*                 mLraVar;
            bool                               mActive;
            bool                               mLinear;
            EvalDoubleIntervalMap::iterator    mIntervalPos;
            
            // interval Bound generation
            std::pair<Updated,Updated>         mBoundsSet; // internal, external
            std::pair<Updated,Updated>         mUpdated; // internal, external
            const smtrat::Formula*             mInternalLeftBound;
            const smtrat::Formula*             mInternalRightBound;
            ModuleInput::iterator              mExternalLeftBound;
            ModuleInput::iterator              mExternalRightBound;
            ModuleInput::iterator              mDefaultPosition;

        private:
            IcpVariable();
            
        public:
            
            /*
             * Constructors
             */
            IcpVariable( carl::Variable::Arg _var, 
                         bool _original, 
                         ModuleInput::iterator _defaultPosition, 
                         EvalDoubleIntervalMap::iterator _intervalPos, 
                         const LRAVariable* _lraVar = NULL ):
                mVar( _var ),
                mOriginal( _original ),
                mCandidates(),
                mLraVar( _lraVar ),
                mActive( false ),
                mLinear( true ),
                mIntervalPos( _intervalPos ),
                mUpdated( std::make_pair(Updated::NONE,Updated::NONE) ),
                mInternalLeftBound( NULL ),
                mInternalRightBound( NULL ),
                mExternalLeftBound( _defaultPosition ),
                mExternalRightBound( _defaultPosition ),
                mDefaultPosition( _defaultPosition )
            {}
            
            ~IcpVariable()
            {}
            
            /*
             * Getter/Setter
             */

            carl::Variable::Arg var() const
            {
                return mVar;
            }

            ContractionCandidates& candidates()
            {
                return mCandidates;
            }

            const LRAVariable* lraVar() const
            {
                return mLraVar;
            }

            void addCandidate( ContractionCandidate* _candidate )
            {
                assert( _candidate->lhs() == mVar );
                mCandidates.insert( mCandidates.end(), _candidate );
                checkLinear();
            }

            void setLraVar( const LRAVariable* _lraVar )
            {
                assert( mLraVar == NULL );
                mLraVar = _lraVar;
                mUpdated = std::make_pair(Updated::BOTH,Updated::BOTH);
            }

            void print( std::ostream& _out = std::cout ) const
            {
                _out << "Original: " << mOriginal << ", " << mVar << ", ";
                if( mLinear && (mLraVar != NULL) )
                {
                    mLraVar->print();
                }
                _out << std::endl;
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
                ContractionCandidates::iterator candidateIt = mCandidates.begin();
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
            
            EvalDoubleIntervalMap::const_iterator intervalPosition() const
            {
                return mIntervalPos;
            }
            
            const DoubleInterval& interval() const
            {
                return mIntervalPos->second;
            }
            
            void setInterval( const DoubleInterval& _interval )
            {
                if( _interval.lowerBoundType() != mIntervalPos->second.lowerBoundType() || _interval.lower() != mIntervalPos->second.lower() )
                {
                    mUpdated.first = (mUpdated.first == Updated::BOTH || mUpdated.first == Updated::RIGHT) ? Updated::BOTH : Updated::LEFT;
                    mUpdated.second = (mUpdated.second == Updated::BOTH || mUpdated.second == Updated::RIGHT) ? Updated::BOTH : Updated::LEFT;
                }
                if( _interval.upperBoundType() != mIntervalPos->second.upperBoundType() || _interval.upper() != mIntervalPos->second.upper() )
                {
                    mUpdated.first = (mUpdated.first == Updated::BOTH || mUpdated.first == Updated::LEFT) ? Updated::BOTH : Updated::RIGHT;
                    mUpdated.second = (mUpdated.second == Updated::BOTH || mUpdated.second == Updated::LEFT) ? Updated::BOTH : Updated::RIGHT;
                }
                mIntervalPos->second = _interval;
            }
            
            void setUnmodified()
            {
                mUpdated = std::make_pair( Updated::NONE, Updated::NONE );
            }
            
            void setExternalUnmodified()
            {
                mUpdated = std::make_pair( mUpdated.first, Updated::NONE );
            }
            
            void setInternalUnmodified()
            {
                mUpdated = std::make_pair( Updated::NONE, mUpdated.second );
            }
            
            Updated isInternalUpdated() const
            {
                return mUpdated.first;
            }
            
            Updated isExternalUpdated() const
            {
                return mUpdated.second;
            }
            
            const smtrat::Formula* internalLeftBound() const
            {
                return mInternalLeftBound;
            }
            
            const smtrat::Formula* internalRightBound() const
            {
                return mInternalRightBound;
            }
            
            ModuleInput::iterator externalLeftBound() const
            {
                return mExternalLeftBound;
            }
            
            ModuleInput::iterator externalRightBound() const
            {
                return mExternalRightBound;
            }
            
            void setInternalLeftBound( const smtrat::Formula* _left )
            {
                mInternalLeftBound = _left;
            }
            
            void setInternalRightBound( const smtrat::Formula* _right )
            {
                mInternalRightBound = _right;
            }
            
            void setExternalLeftBound( ModuleInput::iterator _left )
            {
                mExternalLeftBound = _left;
            }
            
            void setExternalRightBound( ModuleInput::iterator _right )
            {
                mExternalRightBound = _right;
            }
            
            Updated isInternalBoundsSet() const
            {
                if( mInternalLeftBound != NULL )
                {
                    if( mInternalRightBound != NULL )
                        return Updated::BOTH;
                    return Updated::LEFT;
                }
                return Updated::RIGHT;
            }
            
            bool isOriginal() const
            {
                return mOriginal;
            }
            
            /**
             * Checks all candidates if at least one is active - if so, set variable as active.
             * @return true if variable is active
             */
            bool autoActivate()
            {
                ContractionCandidates::iterator candidateIt;
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
            
            bool operator< (IcpVariable const& rhs) const
            {
                return (this->mVar < rhs.var());
            }
            
            friend std::ostream& operator<<( std::ostream& os, const IcpVariable& _var )
            {
                os << _var.var() << " [Orig.: " << _var.isOriginal() << ", act.: " << _var.isActive() << "]";
                if( _var.mLraVar != NULL )
                {
                    os << std::endl;
                    _var.mLraVar->print(os);
                    os << std::endl;
                    _var.mLraVar->printAllBounds(os);
                }
                return os;
            }

        private:

            /*
             * Auxiliary functions
             */
    };
    
    struct icpVariableComp
    {
        bool operator() (const IcpVariable* const _lhs, const IcpVariable* const _rhs ) const
        {
            return (_lhs->var() < _rhs->var());
        }
    };
            
    typedef std::set<const IcpVariable*, icpVariableComp>  set_icpVariable;
}    // namespace icp
} // namespace smtrat
#endif   /* VARIABLE_H */
