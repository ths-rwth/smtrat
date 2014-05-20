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
            const carl::Variable               mVar;
            bool                               mOriginal;
            std::vector<ContractionCandidate*> mCandidates;
            const LRAVariable*                 mLraVar;
            bool                               mActive;
            bool                               mLinear;
            
            // interval Bound generation
            std::pair<Updated,Updated>         mBoundsSet; // internal, external
            std::pair<Updated,Updated>         mUpdated; // internal, external
            const smtrat::Formula*             mInternalLeftBound;
            const smtrat::Formula*             mInternalRightBound;
            ModuleInput::iterator          mExternalLeftBound;
            ModuleInput::iterator          mExternalRightBound;

        private:
            IcpVariable();
            
        public:
            
            /*
             * Constructors
             */
            
            

            IcpVariable( const carl::Variable::Arg _var, bool _original, const LRAVariable* _lraVar = NULL ):
                mVar( _var ),
                mOriginal( _original ),
                mCandidates(),
                mLraVar( _lraVar ),
                mActive( false ),
                mLinear( true ),
                mBoundsSet( std::make_pair(Updated::NONE,Updated::NONE) ),
                mUpdated( std::make_pair(Updated::NONE,Updated::NONE) ),
                mInternalLeftBound ( ),
                mInternalRightBound ( ),
                mExternalLeftBound ( ),
                mExternalRightBound ( )
            {
            }

            IcpVariable( const carl::Variable::Arg _var,
                         bool _original,
                         ContractionCandidate* _candidate,
                         const LRAVariable* _lraVar = NULL ):
                mVar( _var ),
                mOriginal ( _original ),
                mCandidates(),
                mLraVar( _lraVar ),
                mActive( _candidate->isActive() ),
                mLinear( _candidate->isLinear() ),
                mBoundsSet (std::make_pair(Updated::NONE,Updated::NONE)),
                mUpdated( std::make_pair(Updated::NONE,Updated::NONE) ),
                mInternalLeftBound ( ),
                mInternalRightBound ( ),
                mExternalLeftBound ( ),
                mExternalRightBound ( )
            {
                mCandidates.insert( mCandidates.end(), _candidate );
            }
            
            ~IcpVariable()
            {
                switch(mBoundsSet.first)
                {
                    case Updated::LEFT:
                        delete mInternalLeftBound;
                        break;
                    case Updated::RIGHT:
                        delete mInternalRightBound;
                        break;
                    case Updated::BOTH:
                        delete mInternalLeftBound;
                        delete mInternalRightBound;
                        break;
                    default:
                        break;
                }
            }
            
            /*
             * Getter/Setter
             */

            const carl::Variable::Arg var() const
            {
                return mVar;
            }

            std::vector<ContractionCandidate*>& candidates()
            {
                return mCandidates;
            }

            const LRAVariable* lraVar() const
            {
                return mLraVar;
            }

            void addCandidate( ContractionCandidate* _candidate )
            {
                mCandidates.insert( mCandidates.end(), _candidate );
                if( _candidate->isActive() )
                {
                    mActive = true;
                }
                checkLinear();
            }

            void setLraVar( const LRAVariable* _lraVar )
            {
                mLraVar = _lraVar;
                mUpdated = std::make_pair(Updated::BOTH,Updated::BOTH);
            }

            void deleteCandidate( ContractionCandidate* _candidate )
            {
                std::vector<ContractionCandidate*>::iterator candidateIt;
                for( candidateIt = mCandidates.begin(); candidateIt != mCandidates.end(); )
                {
                    if( *candidateIt == _candidate )
                    {
                        candidateIt = mCandidates.erase( candidateIt );
                    }
                    else
                    {
                        ++candidateIt;
                    }
                }
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
            
            void setUpdated(Updated _internal=Updated::BOTH, Updated _external=Updated::BOTH)
            {
                mUpdated = std::make_pair(_internal,_external);
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
                assert(mBoundsSet.first == Updated::LEFT || mBoundsSet.first == Updated::BOTH);
                return mInternalLeftBound;
            }
            
            const smtrat::Formula* internalRightBound() const
            {
                assert(mBoundsSet.first == Updated::RIGHT || mBoundsSet.first == Updated::BOTH);
                return mInternalRightBound;
            }
            
            ModuleInput::iterator externalLeftBound() const
            {
                assert(mBoundsSet.second == Updated::LEFT || mBoundsSet.second == Updated::BOTH);
                return mExternalLeftBound;
            }
            
            ModuleInput::iterator externalRightBound() const
            {
                assert(mBoundsSet.second == Updated::RIGHT || mBoundsSet.second == Updated::BOTH);
                return mExternalRightBound;
            }
            
            void setInternalLeftBound( const smtrat::Formula* _left )
            {
                const smtrat::Formula* toDelete = mInternalLeftBound;
                mInternalLeftBound = _left;
                switch(mBoundsSet.first)
                {
                    case Updated::RIGHT:
                        mBoundsSet.first = Updated::BOTH;
                        break;
                    case Updated::NONE:
                        mBoundsSet.first = Updated::LEFT;
                        break;
                    default:
                        break;
                }
                delete toDelete;
            }
            
            void setInternalRightBound( const smtrat::Formula* _right )
            {
                const smtrat::Formula* toDelete = mInternalRightBound;
                mInternalRightBound = _right;
                switch(mBoundsSet.first)
                {
                    case Updated::LEFT:
                        mBoundsSet.first = Updated::BOTH;
                        break;
                    case Updated::NONE:
                        mBoundsSet.first = Updated::RIGHT;
                        break;
                    default:
                        break;
                }
                delete toDelete;
            }
            
            void setExternalLeftBound( ModuleInput::iterator _left )
            {
                mExternalLeftBound = _left;
                switch(mBoundsSet.second)
                {
                    case Updated::RIGHT:
                        mBoundsSet.second = Updated::BOTH;
                        break;
                    case Updated::NONE:
                        mBoundsSet.second = Updated::LEFT;
                        break;
                    default:
                        break;
                }
            }
            
            void setExternalRightBound( ModuleInput::iterator _right )
            {
                mExternalRightBound = _right;
                switch(mBoundsSet.second)
                {
                    case Updated::LEFT:
                        mBoundsSet.second = Updated::BOTH;
                        break;
                    case Updated::NONE:
                        mBoundsSet.second = Updated::RIGHT;
                        break;
                    default:
                        break;
                }
            }
            
            void boundsSet(Updated _internal=Updated::BOTH, Updated _external=Updated::BOTH)
            {
                mBoundsSet = std::make_pair(_internal,_external);
            }
            
            void internalBoundsSet(Updated _internal=Updated::BOTH)
            {
                mBoundsSet = std::make_pair(_internal,mBoundsSet.second);
                mUpdated = std::pair<Updated,Updated>(Updated::NONE, mUpdated.second);
            }
            
            void externalBoundsSet(Updated _external=Updated::BOTH)
            {
                mBoundsSet = std::make_pair(mBoundsSet.first,_external);
                mUpdated = std::pair<Updated,Updated>(mUpdated.first, Updated::NONE);
            }
            
            Updated isInternalBoundsSet() const
            {
                return mBoundsSet.first;
            }
            
            Updated isExternalBoundsSet() const
            {
                return mBoundsSet.second;
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
