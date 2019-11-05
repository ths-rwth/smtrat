/*
 * File:   HistoryNode.h
 * Author: Stefan Schupp
 *
 * Created on November 9, 2012, 2:02 PM
 */

#pragma once

//#define HISTORY_DEBUG

#include "IcpVariable.h"
#include "ContractionCandidate.h"
#include <smtrat-common/smtrat-common.h>

namespace smtrat
{
    namespace icp
    {
        class HistoryNode
        {
            public:

            private:

                /**
                 *  Members
                 */

                EvalDoubleIntervalMap                          mIntervals;    // intervals AFTER contraction with Candidates of the incoming edge has been applied
                std::map<carl::Variable, std::set<ConstraintT> >  mReasons;
                std::map<carl::Variable, set_icpVariable>      mVariableReasons;
                std::set<const ContractionCandidate*>          mAppliedContractions;
                std::set<ConstraintT>                          mStateInfeasibleConstraints;
                set_icpVariable                                mStateInfeasibleVariables;
                

            public:

                /**
                 *  Methods
                 */

                HistoryNode():
                    mIntervals(),
                    mReasons(),
                    mVariableReasons(),
                    mAppliedContractions(),
                    mStateInfeasibleConstraints(),
                    mStateInfeasibleVariables()
                {}

                HistoryNode( const EvalDoubleIntervalMap& _intervals):
                    mIntervals( _intervals ),
                    mReasons(),
                    mVariableReasons(),
                    mAppliedContractions(),
                    mStateInfeasibleConstraints(),
                    mStateInfeasibleVariables()
                {}

                ~HistoryNode()
                {}

                /**
                 * Getters and Setters
                 */

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
                
                FormulaSetT appliedConstraints()
                {
                    FormulaSetT appliedConstraints;
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
                
                const std::set<ConstraintT>& stateInfeasibleConstraints() const
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
                
                bool addInfeasibleConstraint(const ConstraintT& _constraint, bool _addOnlyConstraint = false)
                {
                    if(!_addOnlyConstraint)
                    {
                        // also add all variables contained in the constraint to stateInfeasibleVariables
                        for( auto variable: _constraint.variables().underlyingVariables() )
                        {
                            if(mVariableReasons.find(variable) != mVariableReasons.end())
                            {
                                for( set_icpVariable::const_iterator icpVarIt = mVariableReasons.at(variable).begin(); icpVarIt != mVariableReasons.at(variable).end(); ++icpVarIt )
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

                const std::set<const ContractionCandidate*>& getCandidates() const
                {
                    return mAppliedContractions;
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
                        for( auto var: _reason.variables().underlyingVariables() )
                        {
                            if( mReasons.find(var) == mReasons.end() )
                                mReasons[var] = std::set<ConstraintT>();
                            addReasons( _variable, mReasons.at( var ) );
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
                
                
                void propagateStateInfeasibleConstraints(HistoryNode* _target) const
                {
                    for( std::set<ConstraintT>::iterator constraintIt = mStateInfeasibleConstraints.begin(); constraintIt != mStateInfeasibleConstraints.end(); ++constraintIt )
                        _target->addInfeasibleConstraint(*constraintIt);
                }
                
                void propagateStateInfeasibleVariables(HistoryNode* _target) const
                {
                    set_icpVariable result;
                    for( set_icpVariable::iterator variableIt = mStateInfeasibleVariables.begin(); variableIt != mStateInfeasibleVariables.end(); ++variableIt )
                    {
                        gatherVariables((*variableIt)->var(), result);
                        for( set_icpVariable::iterator collectedVarIt = result.begin(); collectedVarIt != result.end(); ++collectedVarIt )
                        {
                            _target->addInfeasibleVariable(*collectedVarIt);
                        }
                    }
                }

                void print( std::ostream& _out = std::cout ) const
                {   
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
                
                void reset()
                {
                    mStateInfeasibleConstraints.clear();
                    mStateInfeasibleVariables.clear();
                    mAppliedContractions.clear();
                    mReasons.clear();
                    mVariableReasons.clear();
                }

            private:

                /**
                 *  Functions
                 */
                
                void gatherVariables(carl::Variable::Arg _var, set_icpVariable& _result) const
                {
                    if( mVariableReasons.find(_var) != mVariableReasons.end() )
                    {
//                        std::cout << "search." << std::endl;
                        set_icpVariable variables = mVariableReasons.at(_var);
                        for( set_icpVariable::iterator varIt = variables.begin(); varIt != variables.end(); ++varIt )
                        {
                            if( _result.insert( *varIt ).second )
                            {
//                                std::cout << "Inserted " << (*varIt)->var() << std::endl;
                                gatherVariables((*varIt)->var(), _result);
                            }
                            else
                            {
//                                std::cout << "Already contained: " << (*varIt)->var() << std::endl;
                            }
                        }
                    }
                }
        };    // class HistoryNode
    }    // namespace icp
}    // namespace smtrat
