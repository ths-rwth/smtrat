#include "ContractionCandidateManager.h"

namespace smtrat
{
namespace icp
{   
    ContractionCandidateManager::ContractionCandidateManager():
        mCurrentId(1),
        mCandidates() // TODO: initialize with a certain size
    {}
    
    ContractionCandidate* ContractionCandidateManager::createCandidate (carl::Variable _lhs, 
                                                                        const Poly _rhs,
                                                                        const ConstraintT& _constraint,
                                                                        carl::Variable _derivationVar,
                                                                        Contractor<carl::SimpleNewton>& _contractor,
                                                                        bool _usePropagation)
    {
        ContractionCandidate* tmp = new ContractionCandidate(_lhs, _rhs, _constraint, _derivationVar, _contractor, mCurrentId, _usePropagation);
        
        assert( mCurrentId == mCandidates.size() + 1 );
        mCandidates.push_back( tmp );
        ++mCurrentId;
        
        return tmp;
    }
    
    ContractionCandidate* ContractionCandidateManager::getCandidate( unsigned _id ) const
    {
        if( _id <= mCandidates.size() && _id > 0 )
        {
            return mCandidates[_id - 1];
        }
        return NULL;
    }
    
    void ContractionCandidateManager::closure(const ContractionCandidate* const _candidate, std::set<const ContractionCandidate*>& _candidates) const
    {
        std::pair<std::set<const ContractionCandidate*>::iterator, bool> res = _candidates.insert(_candidate);
        if ( res.second )
        {
//            cout << "[Closure] Add candidate ";
            _candidate->print();
            for( auto symbolIt = _candidate->constraint().variables().begin(); symbolIt != _candidate->constraint().variables().end(); ++symbolIt )
            {
                for( auto candidateIt = mCandidates.begin(); candidateIt != mCandidates.end(); ++candidateIt )
                {
                    if( (*candidateIt)->lhs() == (*symbolIt) )
                    {
                        closure(*candidateIt, _candidates);
                    }
                }
            }
        }
    }
    
} // namespace icp
} // namespace smtrat
