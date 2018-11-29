/* 
 * File:   ContractionCandidateManager.h
 * Author: Stefan Schupp
 *
 * Created on 20. Dezember 2012, 14:26
 */

#pragma once

#include "ContractionCandidate.h"
#include <smtrat-common/smtrat-common.h>

namespace smtrat
{   
namespace icp{
    class ContractionCandidateManager
    {
        
    private:
        
        /**
         * Member variables
         */
        unsigned mCurrentId;
        std::vector<ContractionCandidate*> mCandidates;
        
    public:
        /**
         * Constructors
         */
        
        ContractionCandidateManager();
        
        ~ContractionCandidateManager()
        {
            while( !mCandidates.empty() )
            {
                ContractionCandidate* toDelete = mCandidates.back();
                mCandidates.pop_back();
                delete toDelete;
            }
        }
        
        /**
         * Constructor & Functions
         */
        
        /**
         * Creates a new candidate with an unique id.
         * @param _lhs The slack/nonlinear variable which represents the constraint
         * @param _constraint The constraint which is to be replaced
         * @param _derivationVar The variable from which the derivative is created when performing contraction
         * @param _origin The pointer to the original formula, needed for assertions and removals of subformulas
         * @return a pointer to the created contraction candidate
         */
        ContractionCandidate* createCandidate ( carl::Variable _lhs,
                                                const Poly _rhs,
                                                const ConstraintT& _constraint,
                                                carl::Variable _derivationVar,
                                                Contractor<carl::SimpleNewton>& _contractor,
                                                bool _usePropagation );
        
        /**
         * Returns the id of the given contraction candidate
         * @param _candidate 
         * @return id of the candidate
         */
        unsigned getId ( const ContractionCandidate* const _candidate ) const;
        
        /**
         * Returns the contraction candidate for the given id
         * @param _id
         * @return the pointer to the contraction candidate
         */
        ContractionCandidate* getCandidate ( unsigned _id ) const;
        
        /**
         * Calculates the closure of a certain candidate according to the variables contained.
         * @param _candidate
         * @return the set of candidates in the closure of _candidate
         */
        void closure (const ContractionCandidate* const _candidate, std::set<const ContractionCandidate*>& _candidates) const;
        
        const std::vector<ContractionCandidate*>& candidates()
        {
            return mCandidates;
        }
        
    private:
        /**
         * Auxiliary Functions
         */
        
    }; // class ContractionCandidateManager
    
}// namespace icp
}// namespace smtrat
