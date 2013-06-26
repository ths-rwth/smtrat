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

//#define HISTORY_DEBUG

#include "ContractionCandidate.h"
#include "utils.h"
#include "ICPModule.h"

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

                typedef std::set<const Constraint*>        set_Constraint;
                typedef std::set<const HistoryNode*, comp> set_HistoryNodes;

                struct comp
                {
                    bool operator ()( const HistoryNode* lhs, const HistoryNode* rhs ) const
                    {
                        return lhs->id() < rhs->id();
                    }
                };

            private:

                /**
                 *  Members
                 */

                GiNaCRA::evaldoubleintervalmap                 mIntervals;    // intervals AFTER contraction with Candidates of the incoming edge has been applied
                const Constraint*                              mSplit;
                std::map<string, set_Constraint> mReasons;
                HistoryNode*                                   mLeftChild;
                HistoryNode*                                   mRightChild;
                HistoryNode*                                   mParent;
                std::set<const ContractionCandidate*>          mAppliedContractions;
                const unsigned                                 mId;

            public:

                /**
                 *  Methods
                 */

                HistoryNode( const HistoryNode& _original ):
                    mIntervals( _original.intervals() ),
                    mSplit( _original.split() ),
                    mReasons(),
                    mLeftChild( _original.left() ),
                    mRightChild( _original.right() ),
                    mParent( _original.parent() ),
                    mAppliedContractions( _original.getCandidates() ),
                    mId( _original.id() )
                {}

                HistoryNode( HistoryNode* _parent, unsigned _id ):
                    mIntervals(),
                    mSplit( NULL ),
                    mReasons(),
                    mLeftChild( NULL ),
                    mRightChild( NULL ),
                    mParent( _parent ),
                    mAppliedContractions(),
                    mId( _id )
                {}

                HistoryNode( GiNaCRA::evaldoubleintervalmap _intervals, unsigned _id ):
                    mIntervals( _intervals ),
                    mSplit( NULL ),
                    mReasons(),
                    mLeftChild( NULL ),
                    mRightChild( NULL ),
                    mParent( NULL ),
                    mAppliedContractions(),
                    mId( _id )
                {
                    for( GiNaCRA::evaldoubleintervalmap::iterator intervalIt = _intervals.begin(); intervalIt != _intervals.end(); ++intervalIt )
                    {
                        const symbol var = (*intervalIt).first;
                        std::pair<const Constraint*, const Constraint*> bounds = icp::intervalToConstraint( var, (*intervalIt).second );
                        if( bounds.first != NULL )
                            mReasons[var.get_name()].insert( bounds.first );
                        //                        addReason(var, bounds.first);
                        if( bounds.second != NULL )
                            mReasons[var.get_name()].insert( bounds.second );
                        //                        addReason(var, bounds.second);
                        if( mReasons.find( var.get_name() ) == mReasons.end() )
                            mReasons[var.get_name()] = set_Constraint();
                    }
                }

                HistoryNode( HistoryNode* _parent, GiNaCRA::evaldoubleintervalmap _intervals, unsigned _id ):
                    mIntervals( _intervals ),
                    mSplit( NULL ),
                    mReasons(),
                    mLeftChild( NULL ),
                    mRightChild( NULL ),
                    mParent( _parent ),
                    mAppliedContractions(),
                    mId( _id )
                {
                    for( GiNaCRA::evaldoubleintervalmap::iterator intervalIt = _intervals.begin(); intervalIt != _intervals.end(); ++intervalIt )
                    {
                        std::pair<const Constraint*,
                                  const Constraint*> bounds = icp::intervalToConstraint( (*intervalIt).first, (*intervalIt).second );
                        if( bounds.first != NULL )
                            mReasons[(*intervalIt).first.get_name()].insert( bounds.first );
                        //                        addReason((*intervalIt).first, bounds.first);
                        if( bounds.second != NULL )
                            mReasons[(*intervalIt).first.get_name()].insert( bounds.second );
                        //                        addReason((*intervalIt).first, bounds.second);
                        if( mReasons.find( (*intervalIt).first.get_name() ) == mReasons.end() )
                            mReasons[(*intervalIt).first.get_name()] = set_Constraint();
                    }
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
                    mLeftChild = _child;
                    _child->setParent( this );
                    return _child;
                }

                HistoryNode* addRight( HistoryNode* _child )
                {
                    mRightChild = _child;
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
                    GiNaCRA::evaldoubleintervalmap::const_iterator intervalIt;
                    for( intervalIt = _map.begin(); intervalIt != _map.end(); ++intervalIt )
                    {
                        if( mIntervals.find( (*intervalIt).first ) != mIntervals.end() )
                        {
                            if( mIntervals[(*intervalIt).first] != (*intervalIt).second )
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
                    for( GiNaCRA::evaldoubleintervalmap::const_iterator intervalIt = mIntervals.begin(); intervalIt != mIntervals.end();
                            ++intervalIt )
                    {
                        if( (*intervalIt).second.empty() )
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

                GiNaCRA::DoubleInterval& getInterval( const symbol _variable )
                {
                    assert( mIntervals.find( _variable ) != mIntervals.end() );
                    return mIntervals.at( _variable );
                }

                void addContraction( ContractionCandidate* _candidate )
                {
                    mAppliedContractions.insert( _candidate );
                    // update reasons
                    addReasons( _candidate->lhs(), _candidate->origin() );
                }

                std::set<const ContractionCandidate*> getCandidates() const
                {
                    return mAppliedContractions;
                }

                void setSplit( const Constraint* _split )
                {
                    mSplit = _split;
                }

                const Constraint* split() const
                {
                    return mSplit;
                }

                std::map<string, set_Constraint>& rReasons()
                {
                    return mReasons;
                }

                const std::map<string, set_Constraint>& reasons() const
                {
                    return mReasons;
                }

                set_Constraint& reasons( const symbol _variable )
                {
                    assert( mReasons.find( _variable.get_name() ) != mReasons.end() );
                    return mReasons.at( _variable.get_name() );
                }

                void addReason( string _variable, const Constraint* _reason )
                {
                    if( mReasons.find( _variable ) == mReasons.end() )
                    {
                        mReasons[_variable] = set_Constraint();
                    }
//                    cout << "Try to insert " << *_reason << endl;
                    bool inserted = mReasons.at( _variable ).insert( _reason ).second;
                    if( inserted )
                    {
//                        cout << "[" << _variable << "] Adding reason " << *_reason << endl;
                        for( GiNaC::symtab::const_iterator varIt = _reason->variables().begin(); varIt != _reason->variables().end(); ++varIt )
                        {
                            if( mReasons.find((*varIt).first) == mReasons.end() )
                                mReasons[(*varIt).first] = set_Constraint();
                            addReasons( _variable, mReasons.at( (*varIt).first ) );
                        }
                    }
                    assert( mReasons.find( _variable ) != mReasons.end() );
                }

                void addReasons( string _variable, set_Constraint _reasons )
                {
//                    assert( mReasons.find( _variable ) != mReasons.end() );
                    for( set_Constraint::iterator reasonsIt = _reasons.begin(); reasonsIt != _reasons.end(); ++reasonsIt )
                    {
                        addReason( _variable, (*reasonsIt) );
                    }
                }

                void addReasons( const symbol _variable, std::set<const Formula*> _origins )
                {
                    assert( mReasons.find( _variable.get_name() ) != mReasons.end() );
                    bool                               contained = false;
                    std::set<const Formula*>::iterator minimal   = _origins.begin();
                    for( std::set<const Formula*>::iterator originIt = _origins.begin(); originIt != _origins.end(); ++originIt )
                    {
                        if( mReasons.at( _variable.get_name() ).find( (*originIt)->pConstraint() ) != mReasons.at( _variable.get_name() ).end() )
                        {
                            contained = true;
                            break;
                        }
                        if( (*originIt)->pConstraint()->variables().size() < (*minimal)->pConstraint()->variables().size() )
                        {
                            minimal = originIt;
                        }
                    }
                    if( !contained )
                    {
                        addReason( _variable.get_name(), (*minimal)->pConstraint() );
                    }
                }

                void removeBoundsFromReasons()
                {
                    for( std::map<string, set_Constraint>::iterator variableIt = mReasons.begin(); variableIt != mReasons.end();
                            ++variableIt )
                    {
                        for( set_Constraint::iterator constraintIt = (*variableIt).second.begin(); constraintIt != (*variableIt).second.end(); )
                        {
                            if( isBound( *constraintIt ) )
                                constraintIt = (*variableIt).second.erase( constraintIt );
                            else
                                ++constraintIt;
                        }
                    }
                }

                const symbol variable() const
                {
                    assert( mSplit != NULL );
                    return ex_to<symbol>( (*mSplit->variables().begin()).second );
                }
                
                void propagateReasons() const
                {
                    if( !mParent->isRoot() )
                    {
                        for( std::map<string, set_Constraint>::const_iterator variableIt = mReasons.begin(); variableIt != mReasons.end(); ++variableIt )
                        {
                            mParent->addReasons((*variableIt).first, (*variableIt).second );
                        }
                        mParent->propagateReasons();
                    }
                }

                void removeLeftChild()
                {
                    HistoryNode* toDelete = mLeftChild;
                    mLeftChild = NULL;
                    delete toDelete;
                }

                void removeRightChild()
                {
                    HistoryNode* toDelete = mRightChild;
                    mRightChild = NULL;
                    delete toDelete;
                }

                /**
                 * Return if node is a leaf
                 * @return
                 */
                bool isLeaf() const
                {
                    return (mLeftChild == NULL && mRightChild == NULL);
                }
                
                bool isRoot() const
                {
                    return (mParent == NULL);
                }

                /**
                 * Determines if the node is a leftChild. We define the root as a rightChild.
                 * @return true if node is a leftChild
                 */
                bool isLeft() const
                {
                    if( mParent == NULL )
                    {
                        return false;
                    }
                    return (this == mParent->left());
                }

                /**
                 * Determines if the node is a rightChild. We define the root as a rightChild.
                 * @return true if node is a rightChild
                 */
                bool isRight() const
                {
                    if( mParent == NULL )
                    {
                        return true;
                    }
                    return (this == mParent->right());
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
                    if( mParent != NULL )
                    {
                        _out << "Parent: " << mParent->id() << endl;
                    }
#else
                    _out << "Adress: " << this << endl;
                    if( mParent != NULL )
                    {
                        _out << "Parent: " << mParent << endl;
                    }
#endif
                    _out << "Left:   " << mLeftChild << endl;
                    _out << "Right:  " << mRightChild << endl;
                    if( mSplit != NULL )
                    {
                        _out << "Split in: " << (*mSplit->variables().begin()).second << endl;
                    }
                    else
                    {
                        _out << "Split in: None" << endl;
                    }
                    _out << "Intervals: " << endl;
                    for( GiNaCRA::evaldoubleintervalmap::const_iterator intervalIt = mIntervals.begin(); intervalIt != mIntervals.end();
                            ++intervalIt )
                    {
                        cout << (*intervalIt).first << "\t : ";
                        (*intervalIt).second.dbgprint();
                    }
                    _out << "Applied Contractions: ";
                    if( mAppliedContractions.size() > 0 )
                    {
                        cout << endl;
                        for( std::set<const ContractionCandidate*>::iterator candidateIt = mAppliedContractions.begin();
                                candidateIt != mAppliedContractions.end(); ++candidateIt )
                        {
                            (*candidateIt)->print();
                        }
                    }
                    else
                    {
                        cout << "None" << endl;
                    }
                    printReasons();
                }

                void printReasons( ostream& _out = std::cout ) const
                {
                    _out << "Reasons(" << mReasons.size() << ")" << endl;
                    for( std::map<string, std::set<const Constraint*>>::const_iterator variablesIt = mReasons.begin();
                            variablesIt != mReasons.end(); ++variablesIt )
                    {
                        _out << (*variablesIt).first << ":\t";
                        for( std::set<const Constraint*>::const_iterator reasonIt = (*variablesIt).second.begin();
                                reasonIt != (*variablesIt).second.end(); ++reasonIt )
                        {
                            _out << **reasonIt << ", ";
                        }
                        cout << endl;
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
                void overallContractions( std::set<const ContractionCandidate*>& _candidates ) const
                {
                    if( mParent != NULL )
                    {
                        mParent->overallContractions( _candidates );
                    }
                    for( std::set<const ContractionCandidate*>::iterator ccIt = mAppliedContractions.begin(); ccIt != mAppliedContractions.end();
                            ++ccIt )
                    {
                        _candidates.insert( *ccIt );
                    }
                }

                /**
                 * Returns the number of nodes in the subtree including the actual node.
                 * @return
                 */
                int sizeSubtree() const
                {
                    if( this == NULL )
                    {
                        return 0;
                    }
                    if( this->isLeaf() )
                    {
                        return 1;
                    }
                    else
                    {
                        return mLeftChild->sizeSubtree() + mRightChild->sizeSubtree() + 1;
                    }
                }

                friend bool operator==( HistoryNode const& lhs, HistoryNode const& rhs )
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
                    for( std::set<const ContractionCandidate*>::iterator candidateIt = mAppliedContractions.begin();
                            candidateIt != mAppliedContractions.end(); ++candidateIt )
                    {
                        (*candidateIt)->print();
                    }
#endif
                    std::set<const ContractionCandidate*>::iterator pos = mAppliedContractions.find( _candidate );
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
    }    // namespace icp
}    // namespace smtrat

#endif   /* HISTORYNODE_H */
