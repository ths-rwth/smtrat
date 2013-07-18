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
         * Structs
         */
        struct CCComp
        {           
            bool operator() (const ContractionCandidate* const _lhs, const ContractionCandidate* const _rhs)
            {
                if( (*_lhs->mConstraint->variables().begin()).first < (*_rhs->mConstraint->variables().begin()).first )
                    return true;
                else if( (*_lhs->mConstraint->variables().begin()).first > (*_rhs->mConstraint->variables().begin()).first )
                    return false;
                else if ( _lhs->constraint()->maxDegree((*_lhs->mConstraint->variables().begin()).second) < _rhs->constraint()->maxDegree((*_rhs->mConstraint->variables().begin()).second) )
                    return false;
                else if ( _lhs->constraint()->maxDegree((*_lhs->mConstraint->variables().begin()).second) > _rhs->constraint()->maxDegree((*_rhs->mConstraint->variables().begin()).second) )
                    return true;
                else
                {
                    ex left = _lhs->constraint()->lhs();
                    ex right = _rhs->constraint()->lhs();
                    
                    left /= GiNaC::pow((*_lhs->mConstraint->variables().begin()).second, _lhs->constraint()->maxDegree((*_lhs->mConstraint->variables().begin()).second) );
                    if (left.is_zero())
                        return false;
                    GiNaC::symtab newLeftVariables = _lhs->constraint()->variables();
                    newLeftVariables.erase(newLeftVariables.begin());
                    const Constraint* tmpLeft = Formula::newConstraint(left,_lhs->mConstraint->relation(), newLeftVariables);
                    
                    right /= GiNaC::pow((*_rhs->mConstraint->variables().begin()).second, _rhs->constraint()->maxDegree((*_rhs->mConstraint->variables().begin()).second) );
                    GiNaC::symtab newRightVariables = _rhs->constraint()->variables();
                    newRightVariables.erase(newRightVariables.begin());
                    const Constraint* tmpRight = Formula::newConstraint(right,_rhs->mConstraint->relation(), newRightVariables);
                    
                    ContractionCandidate* lhsCopy = new ContractionCandidate(_lhs->mLhs, tmpLeft, _lhs->mDerivationVar, 0);
                    ContractionCandidate* rhsCopy = new ContractionCandidate(_rhs->mLhs, tmpRight, _lhs->mDerivationVar, 0);
                    
                    bool result = CCComp::operator ()(lhsCopy, rhsCopy);
                    
                    delete lhsCopy;
                    delete rhsCopy;
                    
                    return result;
                }
            }
        };
        
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
        
        /**
         * Reasigns the Ids of the candidates. ATTENTION: This might change the order in which the candidates are processed as well as 
         * any existing mapping, which uses the id of the candidates.
         */
        void reasignIds ();
        
    private:
        /**
         * Auxiliary Functions
         */
        
    }; // class ContractionCandidateManager
    
}// namespace icp
}// namespace smtrat

#endif	/* CONTRACTIONCANDIDATEMANAGER_H */

