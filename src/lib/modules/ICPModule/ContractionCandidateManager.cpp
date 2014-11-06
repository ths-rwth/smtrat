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

#include "ContractionCandidateManager.h"

namespace smtrat
{
    namespace icp{
    ContractionCandidateManager* ContractionCandidateManager::mInstance = NULL;
    
    ContractionCandidateManager::ContractionCandidateManager():
    mCurrentId(1),
    mCandidates() // TODO: initialize with a certain size
    {}
    
    ContractionCandidateManager* ContractionCandidateManager::getInstance()
    {
        if ( mInstance == NULL )
        {
            mInstance = new ContractionCandidateManager();
        }
        return mInstance;
    }
    
    ContractionCandidate* ContractionCandidateManager::createCandidate (carl::Variable _lhs, 
                                                                        const Poly _rhs,
                                                                        const ConstraintT* _constraint,
                                                                        carl::Variable _derivationVar,
                                                                        Contractor<carl::SimpleNewton>& _contractor,
                                                                        const FormulaT& _origin )
    {
        ContractionCandidate* tmp;
        
        // Todo: Is it better to make the replacement here instead of outside?
        if ( _origin.isTrue() )
        {
            tmp = new ContractionCandidate(_lhs, _rhs, _constraint, _derivationVar, _contractor, mCurrentId);
        }
        else
        {
            tmp = new ContractionCandidate(_lhs, _rhs, _constraint, _derivationVar, _contractor, _origin, mCurrentId);    
        }
        
        assert( mCurrentId == mCandidates.size() + 1 );
        mCandidates.push_back( tmp );
        ++mCurrentId;
        
        return tmp;
    }
    
    ContractionCandidate* ContractionCandidateManager::getCandidate( const unsigned _id )
    {
        if( _id <= mCandidates.size() && _id > 0 )
        {
            return mCandidates[_id - 1];
        }
        return NULL;
    }
    
    void ContractionCandidateManager::closure (const ContractionCandidate* const _candidate, std::set<const ContractionCandidate*>& _candidates) const
    {
        std::pair<std::set<const ContractionCandidate*>::iterator, bool> res = _candidates.insert(_candidate);
        if ( res.second )
        {
//            cout << "[Closure] Add candidate ";
            _candidate->print();
            for( auto symbolIt = _candidate->constraint()->variables().begin(); symbolIt != _candidate->constraint()->variables().end(); ++symbolIt )
            {
                for( auto candidateIt = mCandidates.begin(); candidateIt != mCandidates.end(); ++candidateIt )
                {
                    if( (*candidateIt)->lhs() == (*symbolIt) )
                    {
                        mInstance->closure(*candidateIt, _candidates);
                    }
                }
            }
        }
    }
    
} // namespace icp
} // namespace smtrat
