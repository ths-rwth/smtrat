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
            typedef std::set<HistoryNode*, comp>                     set_HistoryNodes;
            
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
#ifdef HISTORY_DEBUG
            unsigned             mId;
#endif

        public:

            /**
             *  Methods
             */

            HistoryNode(){}
            
            HistoryNode( const HistoryNode& _original )
            {
                mParent = _original.parent();
                mIntervals = _original.intervals();
                mLeftChild = _original.left();
                mRightChild = _original.right();
                mSplittingVariable = _original.getSplit();
                mInfeasibleSubset = _original.getInfeasibleSubset();
#ifdef HISTORY_DEBUG
                mId = _original.id();
#endif
                for ( auto intervalIt = _original.intervals().begin(); intervalIt != _original.intervals().end(); ++intervalIt )
                {
                    mIntervals.insert((*intervalIt));
                }
            }

            HistoryNode( HistoryNode* _parent ):
            mIntervals(),
            mSplittingVariable(NULL),
            mAppliedContractions(),
            mInfeasibleSubset()
            {
                mParent       = _parent;
                mLeftChild    = NULL;
                mRightChild   = NULL;
            }

            HistoryNode( GiNaCRA::evaldoubleintervalmap _intervals ):
            mSplittingVariable(NULL),
            mAppliedContractions(),
            mInfeasibleSubset()
            {
                mParent     = NULL;
                mIntervals  = _intervals;
                mLeftChild  = NULL;
                mRightChild = NULL;
            }
            
            HistoryNode( HistoryNode* _parent, GiNaCRA::evaldoubleintervalmap _intervals ):
            mSplittingVariable(NULL),
            mAppliedContractions(),
            mInfeasibleSubset()
            {
                mParent = _parent;
                mIntervals = _intervals;
                mLeftChild = NULL;
                mRightChild = NULL;
            }

            ~HistoryNode()
            {
                if ( mLeftChild != NULL )
                {
                    delete mLeftChild;
                }
                
                if ( mRightChild != NULL )
                {
                    delete mRightChild;
                }
                
                // TODO deleting actions.
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

            bool hasEmptyInterval()
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

            std::set<ContractionCandidate*> getCandidates()
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

            void cutLeft()
            {
                if( mLeftChild->isLeaf() )
                {
                    delete mLeftChild;
                }
                else
                {
                    if( mLeftChild->left() != NULL )
                    {
                        mLeftChild->cutLeft();
                    }
                    if( mLeftChild->right() != NULL )
                    {
                        mLeftChild->cutRight();
                    }
                    delete mLeftChild;
                }
            }

            void cutRight()
            {
                if( mRightChild->isLeaf() )
                {
                    delete mRightChild;
                }
                else
                {
                    if( mRightChild->left() != NULL )
                    {
                        mRightChild->cutLeft();
                    }
                    if( mRightChild->right() != NULL )
                    {
                        mRightChild->cutRight();
                    }
                    delete mRightChild;
                }
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
            
#ifdef HISTORY_DEBUG
            void setId( unsigned _id )
            {
                mId = _id;
            }
            
            const unsigned id() const
            {
                return mId;
            }
#endif
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
                set_HistoryNodes result = std::set<HistoryNode*, comp>();

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
             * Returns the number of nodes in the subtree including the actual node.
             * @return 
             */
            int sizeSubtree() const
            {
                if (this->isLeaf())
                {
                    return 1;
                }
                else
                {
                    return mLeftChild->sizeSubtree() + mRightChild->sizeSubtree() + 1;
                }
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
            void findFirstOccurrence( ContractionCandidate* _candidate, set_HistoryNodes& _result )
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
