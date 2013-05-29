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
 * File:   HistoryNode.h
 * Author: Stefan Schupp
 *
 * Created on November 9, 2012, 2:02 PM
 */

#ifndef HISTORYNODE_H
#define HISTORYNODE_H

#define HISTORY_DEBUG

#include "ContractionCandidate.h"

namespace smtrat
{
    namespace icp
    {
    class HistoryNode
    {
        public:
             /**
             * Typedefs & operators:
             */
        
            struct comp;
            
            typedef std::vector< std::set<Constraint> >              vec_set_Constraint;
            typedef std::set<const HistoryNode*, comp>                     set_HistoryNodes;
            
            struct comp
            {
                bool operator() (const HistoryNode* lhs, const HistoryNode* rhs) const
                {
                    return lhs->id() < rhs->id();
                }
            };
            
        private:

            /**
             *  Members
             */

            GiNaCRA::evaldoubleintervalmap mIntervals;    // intervals AFTER contraction with Candidates of the incoming edge has been applied
            const symbol*              mSplittingVariable;
            HistoryNode*         mLeftChild;
            HistoryNode*         mRightChild;
            HistoryNode*         mParent;
            std::set<ContractionCandidate*> mAppliedContractions;
            vec_set_Constraint   mInfeasibleSubset;
            const unsigned             mId;

        public:

            /**
             *  Methods
             */
            
            HistoryNode( const HistoryNode& _original ):
            mParent(_original.parent()),
            mId(_original.id())
            {
                mIntervals = _original.intervals();
                mLeftChild = _original.left();
                mRightChild = _original.right();
                mSplittingVariable = _original.getSplit();
                mInfeasibleSubset = _original.getInfeasibleSubset();
                for ( auto intervalIt = _original.intervals().begin(); intervalIt != _original.intervals().end(); ++intervalIt )
                {
                    mIntervals.insert((*intervalIt));
                }
            }

            HistoryNode( HistoryNode* _parent, unsigned _id ):
            mIntervals(),
            mSplittingVariable(NULL),
            mAppliedContractions(),
            mInfeasibleSubset(),
            mId(_id)
            {
                mParent       = _parent;
                mLeftChild    = NULL;
                mRightChild   = NULL;
            }

            HistoryNode( GiNaCRA::evaldoubleintervalmap _intervals, unsigned _id ):
            mSplittingVariable(NULL),
            mAppliedContractions(),
            mInfeasibleSubset(),
            mId(_id)
            {
                mParent     = NULL;
                mIntervals  = _intervals;
                mLeftChild  = NULL;
                mRightChild = NULL;
            }
            
            HistoryNode( HistoryNode* _parent, GiNaCRA::evaldoubleintervalmap _intervals, unsigned _id ):
            mSplittingVariable(NULL),
            mAppliedContractions(),
            mInfeasibleSubset(),
            mId(_id)
            {
                mParent = _parent;
                mIntervals = _intervals;
                mLeftChild = NULL;
                mRightChild = NULL;
            }

            ~HistoryNode()
            {
                delete mLeftChild;
                delete mRightChild;
            }

            /**
             * Getters and Setters
             */

            /**
             * Return left child
             * @return
             */
            HistoryNode* left() const
            {
                return mLeftChild;
            }

            /**
             * Return right child
             * @return
             */
            HistoryNode* right() const
            {
                return mRightChild;
            }

            HistoryNode* addLeft( HistoryNode* _child )
            {
                mLeftChild        = _child;
                _child->setParent( this );
                return _child;
            }

            HistoryNode* addRight( HistoryNode* _child )
            {
                mRightChild        = _child;
                _child->setParent( this );
                return _child;
            }

            HistoryNode* parent() const
            {
                return mParent;
            }

            void setParent( HistoryNode* _parent )
            {
                this->mParent = _parent;
            }

            const GiNaCRA::evaldoubleintervalmap& intervals() const
            {
                return mIntervals;
            }
            
            GiNaCRA::evaldoubleintervalmap& rIntervals()
            {
                return mIntervals;
            }

            void setIntervals( GiNaCRA::evaldoubleintervalmap _map )
            {
                GiNaCRA::evaldoubleintervalmap::iterator intervalIt;
                for ( intervalIt = _map.begin(); intervalIt != _map.end(); ++intervalIt )
                {
                    if ( mIntervals.find((*intervalIt).first) != mIntervals.end() )
                    {
                        if ( mIntervals[(*intervalIt).first] != (*intervalIt).second )
                        {
                            mIntervals[(*intervalIt).first] = (*intervalIt).second;
                        }
                    }
                    else
                    {
                        mIntervals[(*intervalIt).first] = (*intervalIt).second;
                    }
                }
            }

            bool hasEmptyInterval() const
            {
                for(auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                {
                    if ( (*intervalIt).second.empty() )
                    {
                        return true;
                    }
                }
                return false;
            }
            
            /**
             * updates or inserts an interval into the actual map
             * @param _var
             * @param _interval
             * @return true if only an update
             */
            bool addInterval( GiNaC::symbol _var, GiNaCRA::DoubleInterval _interval )
            {
                if( mIntervals.find( _var ) != mIntervals.end() )
                {
                    mIntervals[_var] = _interval;
                    return true;
                }
                else
                {
                    mIntervals[_var] = _interval;
                    return false;
                }
            }

            GiNaCRA::DoubleInterval& getInterval ( const symbol _variable )
            {
                return mIntervals[_variable];
            }
            
            void addContraction( ContractionCandidate* _candidate )
            {
                mAppliedContractions.insert( _candidate );
            }

            std::set<ContractionCandidate*> getCandidates() const
            {
                return mAppliedContractions;
            }

            void setSplit( const symbol* _var )
            {
                mSplittingVariable = _var;
            }

            const symbol* getSplit() const
            {
                return mSplittingVariable;
            }
            
            void setInfeasibleSubset( vec_set_Constraint _set )
            {
                mInfeasibleSubset = _set;
            }
            
            vec_set_Constraint getInfeasibleSubset () const
            {
                return mInfeasibleSubset;
            }

            void removeLeftChild()
            {
                mLeftChild = NULL;
            }
            
            void removeRightChild()
            {
                mRightChild = NULL;
            }
            
            /**
             * Return if node is a leaf
             * @return
             */
            bool isLeaf() const
            {
                return (mLeftChild == NULL && mRightChild == NULL);
            }

            /**
             * Determines if the node is a leftChild. We define the root as a rightChild.
             * @return true if node is a leftChild
             */
            bool isLeft() const
            {
                if ( mParent == NULL )
                {
                    return false;
                }
                return ( this == mParent->left() );
            }

            /**
             * Determines if the node is a rightChild. We define the root as a rightChild.
             * @return true if node is a rightChild
             */
            bool isRight() const
            {
                if ( mParent == NULL )
                {
                    return true;
                }
                return ( this == mParent->right() );
            }
            
            const unsigned id() const
            {
                return mId;
            }
            /**
             * Print current node
             * @param _out
             */
            void print( ostream& _out = std::cout ) const
            {
#ifdef HISTORY_DEBUG
                _out << "Id: " << this->mId << endl;
                if ( mParent != NULL)
                {
                    _out << "Parent: " << mParent->id() << endl;    
                }
#else
                _out << "Adress: " << this << endl;
                if ( mParent != NULL)
                {
                    _out << "Parent: " << mParent << endl;
                }
#endif
                _out << "Left:   " << mLeftChild << endl;
                _out << "Right:  " << mRightChild << endl;
                if (mSplittingVariable != NULL)
                {
                    _out << "Split in: " << mSplittingVariable << endl;    
                }
                else
                {
                    _out << "Split in: None" << endl;
                }
                _out << "Intervals: " << endl;
                for ( auto intervalIt = mIntervals.begin(); intervalIt != mIntervals.end(); ++intervalIt )
                {
                    cout << (*intervalIt).first << "\t : ";
                    (*intervalIt).second.dbgprint();
                }
                _out << "Applied Contractions: ";
                if ( mAppliedContractions.size() > 0 )
                {
                    cout << endl;
                    for ( auto candidateIt = mAppliedContractions.begin(); candidateIt != mAppliedContractions.end(); ++candidateIt )
                    {
                        (*candidateIt)->print();
                    }
                }
                else
                {
                    cout << "None" << endl;
                }
                
            }

            /**
             * Search for Candidates in the tree below this node.
             * @param _candidate The candidate which is to be found
             * @return a list of pointers to the first nodes which have the candidate in their contraction sequence
             */
            set_HistoryNodes findCandidates( ContractionCandidate* _candidate ) const
            {
                set_HistoryNodes result = set_HistoryNodes();

                if( mLeftChild != NULL )
                {
                    mLeftChild->findFirstOccurrence( _candidate, result );
                }
                if( mRightChild != NULL )
                {
                    mRightChild->findFirstOccurrence( _candidate, result );
                }

                return result;
            }
            
            /**
             * Creates a set of contraction candidate pointers from the candidates which have been used so far since the last reset of the tree.
             * @param _candidates Reference to the resulting set of contraction candidate pointers.
             */
            void overallContractions(std::set<ContractionCandidate*>& _candidates) const
            {
                if ( mParent != NULL)
                {
                    mParent->overallContractions(_candidates);
                }
                for ( std::set<ContractionCandidate*>::iterator ccIt = mAppliedContractions.begin(); ccIt != mAppliedContractions.end(); ++ccIt )
                {
                    _candidates.insert(*ccIt);
                }
            }
            
            /**
             * Returns the number of nodes in the subtree including the actual node.
             * @return 
             */
            int sizeSubtree() const
            {
                if (this == NULL)
                {
                    return 0;
                }
                if (this->isLeaf())
                {
                    return 1;
                }
                else
                {
                    return mLeftChild->sizeSubtree() + mRightChild->sizeSubtree() + 1;
                }
            }
            
            friend bool operator== (HistoryNode const& lhs, HistoryNode const& rhs)
            {
                return lhs.id() == rhs.id();
            }

        private:

            /**
             *  Functions
             */
            
            /**
             * Find first occurrence of the contractionCandidate below this node
             * @param _candidate
             * @return pointer to Node
             */
            void findFirstOccurrence( ContractionCandidate* _candidate, set_HistoryNodes& _result ) const
            {
#ifdef HISTORY_DEBUG
                cout << "searching for ";
                _candidate->print();
                cout << "#contractions in " << mId << ": " << mAppliedContractions.size() << endl;
                for ( auto candidateIt = mAppliedContractions.begin(); candidateIt != mAppliedContractions.end(); ++candidateIt )
                {
                    (*candidateIt)->print();
                }
#endif
                std::set<ContractionCandidate*>::iterator pos = mAppliedContractions.find( _candidate );
                if( pos != mAppliedContractions.end() )
                {
#ifdef HISTORY_DEBUG
                    cout << "Found candidate" << (*pos)->id() << " in node " << mId << ": ";
                    (*pos)->print();
#endif
                    _result.insert( this );
                }
                else
                {
                    if( mLeftChild != NULL )
                    {
                        mLeftChild->findFirstOccurrence( _candidate, _result );
                    }
                    if( mRightChild != NULL )
                    {
                        mRightChild->findFirstOccurrence( _candidate, _result );
                    }
                }
            }
    };    // class HistoryNode
    } // namespace icp
}    // namespace smtrat

#endif   /* HISTORYNODE_H */
