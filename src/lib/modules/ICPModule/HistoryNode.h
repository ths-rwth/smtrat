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

#include "IcpVariable.h"
#include "ContractionCandidate.h"
#include "../../Common.h"

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
                struct comp
                {
                    bool operator ()( const HistoryNode* lhs, const HistoryNode* rhs ) const
                    {
                        return lhs->id() < rhs->id();
                    }
                };
                
                typedef std::set<const HistoryNode*, comp> set_HistoryNode;

            private:

                /**
                 *  Members
                 */

                EvalDoubleIntervalMap                          mIntervals;    // intervals AFTER contraction with Candidates of the incoming edge has been applied
                ConstraintT                                    mSplit;
                std::map<carl::Variable, std::set<ConstraintT> >  mReasons;
                std::map<carl::Variable, set_icpVariable>      mVariableReasons;
                HistoryNode*                                   mLeftChild;
                HistoryNode*                                   mRightChild;
                HistoryNode*                                   mParent;
                std::set<const ContractionCandidate*>          mAppliedContractions;
                std::set<ConstraintT>                          mStateInfeasibleConstraints;
                set_icpVariable                                mStateInfeasibleVariables;
                const unsigned                                 mId;
                

            public:

                /**
                 *  Methods
                 */

                HistoryNode( HistoryNode* _parent, unsigned _id ):
                    mIntervals(),
                    mSplit(),
                    mReasons(),
                    mVariableReasons(),
                    mLeftChild( NULL ),
                    mRightChild( NULL ),
                    mParent( _parent ),
                    mAppliedContractions(),
                    mStateInfeasibleConstraints(),
                    mStateInfeasibleVariables(),
                    mId( _id )
                {}

                HistoryNode( const EvalDoubleIntervalMap& _intervals, unsigned _id ):
                    mIntervals( _intervals ),
                    mSplit(),
                    mReasons(),
                    mVariableReasons(),
                    mLeftChild( NULL ),
                    mRightChild( NULL ),
                    mParent( NULL ),
                    mAppliedContractions(),
                    mStateInfeasibleConstraints(),
                    mStateInfeasibleVariables(),
                    mId( _id )
                {}

                HistoryNode( HistoryNode* _parent, const EvalDoubleIntervalMap& _intervals, unsigned _id ):
                    mIntervals( _intervals ),
                    mSplit(),
                    mReasons(),
                    mVariableReasons(),
                    mLeftChild( NULL ),
                    mRightChild( NULL ),
                    mParent( _parent ),
                    mAppliedContractions(),
                    mStateInfeasibleConstraints(),
                    mStateInfeasibleVariables(),
                    mId( _id )
                {}

                ~HistoryNode()
                {
                    if(mLeftChild != NULL)
                        delete mLeftChild;
                    if(mRightChild != NULL)
                        delete mRightChild;
                }

                /**
                 * Getters and Setters
                 */

                HistoryNode* left() const
                {
                    return mLeftChild;
                }

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
                
                carl::Variable::Arg variable() const
                {
                    assert( mSplit != ConstraintT() );
                    return (*mSplit.variables().begin());
                }

                const EvalDoubleIntervalMap& intervals() const
                {
                    return mIntervals;
                }

                EvalDoubleIntervalMap& rIntervals()
                {
                    return mIntervals;
                }

                DoubleInterval& getInterval( carl::Variable::Arg _variable )
                {
                    assert( mIntervals.find( _variable ) != mIntervals.end() );
                    return mIntervals.at( _variable );
                }
                
                void setIntervals( const EvalDoubleIntervalMap& _map )
                {
                    EvalDoubleIntervalMap::const_iterator intervalIt;
                    for( intervalIt = _map.begin(); intervalIt != _map.end(); ++intervalIt )
                    {
                        if( mIntervals.find( (*intervalIt).first ) != mIntervals.end() )
                        {
                            if( mIntervals.at((*intervalIt).first) != (*intervalIt).second )
                                mIntervals[(*intervalIt).first] = (*intervalIt).second;
                        }
                        else
                            mIntervals[(*intervalIt).first] = (*intervalIt).second;
                    }
                }
                
                /**
                 * updates or inserts an interval into the actual map
                 * @param _var
                 * @param _interval
                 * @return true if only an update
                 */
                bool addInterval( carl::Variable::Arg _var, const DoubleInterval& _interval )
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

                bool hasEmptyInterval() const
                {
                    for( EvalDoubleIntervalMap::const_iterator intervalIt = mIntervals.begin(); intervalIt != mIntervals.end();
                            ++intervalIt )
                    {
                        if( (*intervalIt).second.isEmpty() )
                            return true;
                    }
                    return false;
                }
                
                std::set<const ContractionCandidate*> appliedContractions()
                {
                    return mAppliedContractions;
                }
                
                FormulasT appliedConstraints()
                {
                    FormulasT appliedConstraints;
                    for( std::set<const ContractionCandidate*>::iterator candidateIt = mAppliedContractions.begin(); candidateIt != mAppliedContractions.end(); ++candidateIt )
                    {
                        for( auto originIt = (*candidateIt)->origin().begin(); originIt != (*candidateIt)->origin().end(); ++originIt )
                        {
                            appliedConstraints.insert(*originIt);
                        }
                    }
                    return appliedConstraints;
                }
                
                void appliedConstraints( std::vector<FormulaT>& _result )
                {
                    for( std::set<const ContractionCandidate*>::iterator candidateIt = mAppliedContractions.begin(); candidateIt != mAppliedContractions.end(); ++candidateIt )
                    {
                        for( auto originIt = (*candidateIt)->origin().begin(); originIt != (*candidateIt)->origin().end(); ++originIt )
                        {
                            _result.push_back(*originIt);
                        }
                    }
                }

                std::set<ConstraintT>& rStateInfeasibleConstraints()
                {
                    return mStateInfeasibleConstraints;
                }
                
                std::set<ConstraintT> stateInfeasibleConstraints() const
                {
                    return mStateInfeasibleConstraints;
                }
                
                set_icpVariable& rStateInfeasibleVariables()
                {
                    return mStateInfeasibleVariables;
                }
                
                set_icpVariable stateInfeasibleVariables() const
                {
                    return mStateInfeasibleVariables;
                }

                bool stateInfeasibleConstraintsContainSplit()
                {
                    for( set_icpVariable::const_iterator variableIt = mStateInfeasibleVariables.begin(); variableIt != mStateInfeasibleVariables.end(); ++variableIt )
                    {
                        if( (*variableIt)->var() == this->variable() )
                        {
                            return true;
                        }
                    }
                    return false;
                }
                
                bool addInfeasibleConstraint(const ConstraintT& _constraint, bool _addOnlyConstraint = false)
                {
                    if(!_addOnlyConstraint)
                    {
                        // also add all variables contained in the constraint to stateInfeasibleVariables
                        for( auto variableIt = _constraint.variables().begin(); variableIt != _constraint.variables().end(); ++variableIt )
                        {
                            if(mVariableReasons.find(*variableIt) != mVariableReasons.end())
                            {
                                for( set_icpVariable::const_iterator icpVarIt = mVariableReasons.at(*variableIt).begin(); icpVarIt != mVariableReasons.at(*variableIt).end(); ++icpVarIt )
                                    addInfeasibleVariable(*icpVarIt);
                            }
                        }
                    }
                    return mStateInfeasibleConstraints.insert(_constraint).second;
                }
                
                bool addInfeasibleVariable( const IcpVariable* _variable, bool _addOnlyVariable = false )
                {
                    if(!_addOnlyVariable)
                    {
                        //also add the reasons for the variables
                        if (mVariableReasons.find(_variable->var()) != mVariableReasons.end())
                        {
                            for( set_icpVariable::iterator variableIt = mVariableReasons.at(_variable->var()).begin(); variableIt != mVariableReasons.at(_variable->var()).end(); ++variableIt )
                                mStateInfeasibleVariables.insert(*variableIt);
                        }
                    }
                    return mStateInfeasibleVariables.insert(_variable).second;
                }

                void addContraction( ContractionCandidate* _candidate, const set_icpVariable& _variables )
                {
                    mAppliedContractions.insert( _candidate );
                    
                    for( set_icpVariable::iterator variableIt = _variables.begin(); variableIt != _variables.end(); ++variableIt )
                        addVariableReason( _candidate->derivationVar(), *variableIt );
                    
                    // update reasons
                    assert(!_candidate->origin().empty());
                    // TEMPORARY!!! -> Very coarse overapprox!
                    for( auto originIt = _candidate->rOrigin().begin(); originIt != _candidate->rOrigin().end(); ++originIt )
                        addReason( _candidate->derivationVar(), originIt->constraint() );
                }

                std::set<const ContractionCandidate*> getCandidates() const
                {
                    return mAppliedContractions;
                }

                void setSplit( const ConstraintT& _split )
                {
                    mSplit = _split;
                }

                const ConstraintT& split() const
                {
                    return mSplit;
                }

                std::map<carl::Variable, std::set<ConstraintT>>& rReasons()
                {
                    return mReasons;
                }

                const std::map<carl::Variable, std::set<ConstraintT>>& reasons() const
                {
                    return mReasons;
                }


                std::set<ConstraintT>& reasons( carl::Variable::Arg _variable )
                {
                    assert( mReasons.find( _variable ) != mReasons.end() );
                    return mReasons.at( _variable );
                }

                void addReason( carl::Variable::Arg _variable, const ConstraintT& _reason )
                {
                    if( mReasons.find( _variable ) == mReasons.end() )
                        mReasons[_variable] = std::set<ConstraintT>();
                    
                    bool inserted = mReasons.at( _variable ).insert( _reason ).second;
                    if( inserted )
                    {
                        for( auto varIt = _reason.variables().begin(); varIt != _reason.variables().end(); ++varIt )
                        {
                            if( mReasons.find(*varIt) == mReasons.end() )
                                mReasons[*varIt] = std::set<ConstraintT>();
                            addReasons( _variable, mReasons.at( *varIt ) );
                        }
                    }
                    assert( mReasons.find( _variable ) != mReasons.end() );
                }

                void addReasons( carl::Variable::Arg _variable, const std::set<ConstraintT>& _reasons )
                {
                    for( std::set<ConstraintT>::iterator reasonsIt = _reasons.begin(); reasonsIt != _reasons.end(); ++reasonsIt )
                        addReason( _variable, (*reasonsIt) );
                }

                void addReasons( carl::Variable::Arg _variable, const FormulasT& _origins )
                {
                    assert( mReasons.find( _variable ) != mReasons.end() );
                    bool                               contained = false;
                    auto minimal = _origins.begin();
                    for( auto originIt = _origins.begin(); originIt != _origins.end(); ++originIt )
                    {
                        if( mReasons.at( _variable ).find( originIt->constraint() ) != mReasons.at( _variable ).end() )
                        {
                            contained = true;
                            break;
                        }
                        if( originIt->constraint().variables().size() < minimal->constraint().variables().size() )
                            minimal = originIt;
                    }
                    if( !contained )
                        addReason( _variable, minimal->constraint() );
                }
                
                void addVariableReason( carl::Variable::Arg _variable, const IcpVariable* _reason )
                {
                    mVariableReasons[_variable].insert(_reason);
                }
                
                void addVariableReasons( carl::Variable::Arg _variable, set_icpVariable _variables )
                {
                    for( set_icpVariable::iterator variableIt = _variables.begin(); variableIt != _variables.end(); ++variableIt )
                        mVariableReasons[_variable].insert(*variableIt);
                }
                
                const std::map<carl::Variable, set_icpVariable>& variableReasons()
                {
                    return mVariableReasons;
                }
                
                std::map<carl::Variable, set_icpVariable>& rVariableReasons()
                {
                    return mVariableReasons;
                }
                
                set_icpVariable variableReasons( carl::Variable::Arg _variable )
                {
                    assert(mVariableReasons.find(_variable) != mVariableReasons.end());
                    return mVariableReasons.at(_variable);
                }
                
                
                void variableHull( carl::Variable::Arg _variable, set_icpVariable& _result ) const
                {
                    gatherVariables(_variable, _result);
                }
                
                
                void propagateStateInfeasibleConstraints() const
                {
                    if( !this->isRoot() )
                    {
                        for( std::set<ConstraintT>::iterator constraintIt = mStateInfeasibleConstraints.begin(); constraintIt != mStateInfeasibleConstraints.end(); ++constraintIt )
                            mParent->addInfeasibleConstraint(*constraintIt);
                        
                        mParent->propagateStateInfeasibleConstraints();
                    }
                }
                
                void propagateStateInfeasibleVariables() const
                {
                    if( !this->isRoot() )
                    {
                        set_icpVariable result;
                        for( set_icpVariable::iterator variableIt = mStateInfeasibleVariables.begin(); variableIt != mStateInfeasibleVariables.end(); ++variableIt )
                        {
                            gatherVariables((*variableIt)->var(), result);
                            for( set_icpVariable::iterator collectedVarIt = result.begin(); collectedVarIt != result.end(); ++collectedVarIt )
                            {
                                mParent->addInfeasibleVariable(*collectedVarIt);
                            }
                        }
                        
                        
                        mParent->propagateStateInfeasibleVariables();
                    }
                }

                void removeLeftChild()
                {
                    delete mLeftChild;
                    mLeftChild = NULL;
                }

                void removeRightChild()
                {
                    delete mRightChild;
                    mRightChild = NULL;
                }

                bool isLeaf() const
                {
                    return (mLeftChild == NULL && mRightChild == NULL);
                }
                
                bool isRoot() const
                {
                    return (mParent == NULL);
                }

                bool isLeft() const
                {
                    if( mParent == NULL )
                        return false;
                    
                    return (this == mParent->left());
                }

                bool isRight() const
                {
                    if( mParent == NULL )
                        return true;
                    
                    return (this == mParent->right());
                }

                unsigned id() const
                {
                    return mId;
                }

                void print( std::ostream& _out = std::cout ) const
                {
#ifdef HISTORY_DEBUG
                    _out << "Id: " << this->mId << endl;
                    if( mParent != NULL )
                        _out << "Parent: " << mParent->id() << std::endl;
                    
#else
                    _out << "Adress: " << this << std::endl;
                    if( mParent != NULL )
                    {
                        _out << "Parent: " << mParent << std::endl;
                    }
#endif
                    _out << "Left:   " << mLeftChild << std::endl;
                    _out << "Right:  " << mRightChild << std::endl;
                    if( mSplit != ConstraintT() )
                        _out << "Split in: " << (*mSplit.variables().begin()) << std::endl;
                    else
                        _out << "Split in: None" << std::endl;
                    
                    _out << "Intervals: " << std::endl;
                    for( EvalDoubleIntervalMap::const_iterator intervalIt = mIntervals.begin(); intervalIt != mIntervals.end();
                            ++intervalIt )
                    {
                        _out << (*intervalIt).first << "\t : " << (*intervalIt).second << std::endl;
                    }
                    _out << "Applied Contractions: ";
                    if( mAppliedContractions.size() > 0 )
                    {
                        _out << std::endl;
                        for( std::set<const ContractionCandidate*>::iterator candidateIt = mAppliedContractions.begin();
                                candidateIt != mAppliedContractions.end(); ++candidateIt )
                        {
                            (*candidateIt)->print();
                        }
                    }
                    else
                        _out << "None" << std::endl;
                    _out << "Infeasible Variables: ";
                    if( !mStateInfeasibleVariables.empty())
                    {
                        _out << std::endl;
                        for( set_icpVariable::iterator varIt = mStateInfeasibleVariables.begin(); varIt != mStateInfeasibleVariables.end(); ++varIt )
                        (*varIt)->print();
                    }
                    else
                    {
                        _out << "None" << std::endl;
                    }
                    
                    _out << "Infeasible Constraints: ";
                    if( !mStateInfeasibleConstraints.empty() )
                    {
                        _out << std::endl;
                        for( std::set<ConstraintT>::iterator constraintIt = mStateInfeasibleConstraints.begin(); constraintIt != mStateInfeasibleConstraints.end(); ++constraintIt )
                            _out << *constraintIt << std::endl;
                    }
                    else
                    {
                        _out << "None" << std::endl;
                    }
//                    printReasons();
                }

                void printReasons( std::ostream& _out = std::cout ) const
                {
                    _out << "Reasons(" << mReasons.size() << ")" << std::endl;
                    for( std::map<carl::Variable, std::set<ConstraintT> >::const_iterator variablesIt = mReasons.begin();
                            variablesIt != mReasons.end(); ++variablesIt )
                    {
                        _out << (*variablesIt).first << ":\t";
                        for( std::set<ConstraintT>::const_iterator reasonIt = (*variablesIt).second.begin(); reasonIt != (*variablesIt).second.end(); ++reasonIt )
                        {
                            _out << *reasonIt << ", ";
                        }
                        _out << std::endl;
                    }
                }
                
                void printVariableReasons( std::ostream& _out = std::cout ) const
                {
                    _out << "VariableReasons(" << mVariableReasons.size() << ")" << std::endl;
                    for( std::map<carl::Variable, set_icpVariable>::const_iterator variablesIt = mVariableReasons.begin();
                            variablesIt != mVariableReasons.end(); ++variablesIt )
                    {
                        _out << (*variablesIt).first << ":\t";
                        for( set_icpVariable::const_iterator reasonIt = (*variablesIt).second.begin();
                                reasonIt != (*variablesIt).second.end(); ++reasonIt )
                        {
                            _out << **reasonIt << ", ";
                        }
                        std::cout << std::endl;
                    }
                }

                /**
                 * Search for Candidates in the tree below this node.
                 * @param _candidate The candidate which is to be found
                 * @return a list of pointers to the first nodes which have the candidate in their contraction sequence
                 */
                set_HistoryNode findCandidates( ContractionCandidate* _candidate ) const
                {
                    set_HistoryNode result = set_HistoryNode();

                    if( mLeftChild != NULL )
                        mLeftChild->findFirstOccurrence( _candidate, result );
                    if( mRightChild != NULL )
                        mRightChild->findFirstOccurrence( _candidate, result );

                    return result;
                }

                /**
                 * Creates a set of contraction candidate pointers from the candidates which have been used so far since the last reset of the tree.
                 * @param _candidates Reference to the resulting set of contraction candidate pointers.
                 */
                void overallContractions( std::set<const ContractionCandidate*>& _candidates ) const
                {
                    if( mParent != NULL )
                        mParent->overallContractions( _candidates );
                    
                    for( std::set<const ContractionCandidate*>::iterator ccIt = mAppliedContractions.begin(); ccIt != mAppliedContractions.end();
                            ++ccIt )
                        _candidates.insert( *ccIt );
                }

                /**
                 * Returns the number of nodes in the subtree including the actual node.
                 * @return
                 */
                int sizeSubtree() const
                {
					int size = 1;
                    if (mLeftChild != NULL)
                        size += mLeftChild->sizeSubtree();
					if (mRightChild != NULL)
						size += mRightChild->sizeSubtree();
					return size;
                }
                
                void reset()
                {
                    mStateInfeasibleConstraints.clear();
                    mStateInfeasibleVariables.clear();
                    mAppliedContractions.clear();
                    mReasons.clear();
                    mVariableReasons.clear();
                }

                friend bool operator==( HistoryNode const& lhs, HistoryNode const& rhs )
                {
                    return lhs.mId == rhs.mId;
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
                void findFirstOccurrence( ContractionCandidate* _candidate, set_HistoryNode& _result ) const
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
                        std::cout << "Found candidate" << (*pos)->id() << " in node " << mId << ": ";
                        (*pos)->print();
#endif
                        _result.insert( this );
                    }
                    else
                    {
                        if( mLeftChild != NULL )
                            mLeftChild->findFirstOccurrence( _candidate, _result );
                        if( mRightChild != NULL )
                            mRightChild->findFirstOccurrence( _candidate, _result );
                    }
                }
                
                void gatherVariables(carl::Variable::Arg _var, set_icpVariable& _result) const
                {
                    if( mVariableReasons.find(_var) != mVariableReasons.end() )
                    {
//                        cout << "search." << endl;
                        set_icpVariable variables = mVariableReasons.at(_var);
                        for( set_icpVariable::iterator varIt = variables.begin(); varIt != variables.end(); ++varIt )
                        {
                            if( _result.insert( *varIt ).second )
                            {
//                                cout << "Inserted " << (*varIt)->var() << endl;
                                gatherVariables((*varIt)->var(), _result);
                            }
                            else
                            {
//                                cout << "Already contained: " << (*varIt)->var() << endl;
                            }
                        }
                    }
                }
        };    // class HistoryNode
    }    // namespace icp
}    // namespace smtrat

#endif   /* HISTORYNODE_H */
