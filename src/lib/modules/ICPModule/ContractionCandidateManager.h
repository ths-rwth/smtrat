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
 * File:   ContractionCandidateManager.h
 * Author: Stefan Schupp
 *
 * Created on 20. Dezember 2012, 14:26
 */

#ifndef CONTRACTIONCANDIDATEMANAGER_H
#define	CONTRACTIONCANDIDATEMANAGER_H

#include "ContractionCandidate.h"

namespace smtrat
{   
    namespace icp{
    class ContractionCandidateManager
    {
    private:
        
        /**
         * Member variables
         */
        static ContractionCandidateManager* mInstance;
        unsigned mCurrentId;
        std::map<unsigned, ContractionCandidate*> mCandidates;
        
        /**
         * Constructors
         */
        
        ContractionCandidateManager();
        
        ~ContractionCandidateManager()
        {
            clearCandidates();
        }
        
    public:
        /**
         * Constructor & Functions
         */
        
        /**
         * Returns the instance of the Manager
         */
        ContractionCandidateManager* getInstance();
        
        /**
         * Creates a new candidate with an unique id.
         * @param _lhs The slack/nonlinear variable which represents the constraint
         * @param _constraint The constraint which is to be replaced
         * @param _derivationVar The variable from which the derivative is created when performing contraction
         * @param _origin The pointer to the original formula, needed for assertions and removals of subformulas
         * @return a pointer to the created contraction candidate
         */
        ContractionCandidate* createCandidate ( symbol _lhs, const Constraint* _constraint, symbol _derivationVar, const Formula* _origin = NULL );
        
        /**
         * Returns the id of the given contraction candidate
         * @param _candidate 
         * @return id of the candidate
         */
        const unsigned getId ( const ContractionCandidate* const _candidate ) const;
        
        /**
         * Returns the contraction candidate for the given id
         * @param _id
         * @return the pointer to the contraction candidate
         */
        ContractionCandidate* getCandidate ( const unsigned _id );
        
        /**
         * Removes a candidate from the list
         * @param _candidate
         */
        void removeCandidate ( ContractionCandidate* _candidate );
        
        /**
         * deletes all candidates.
         */
        void clearCandidates ();
        
        /**
         * Calculates the closure of a certain candidate according to the variables contained.
         * @param _candidate
         * @return the set of candidates in the closure of _candidate
         */
        void closure (const ContractionCandidate* const _candidate, std::set<const ContractionCandidate*>& _candidates) const;
        
        std::map<unsigned, ContractionCandidate*>& rCandidates()
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

#endif	/* CONTRACTIONCANDIDATEMANAGER_H */

