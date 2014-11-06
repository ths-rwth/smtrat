/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2013 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT. If not, see <http://www.gnu.org/licenses/>.
 *
 */

/**
 * @file StrategyGraph.cpp
 *
 * @author  Henrik Schmitz
 * @since   2012-09-10
 * @version 2013-01-31
 */

#include "StrategyGraph.h"

using namespace std;

namespace smtrat
{
    size_t StrategyGraph::Edge::mPriorityAllocator = 1;

    StrategyGraph::StrategyGraph():
        mStrategyGraph(),
        mNumberOfBranches( 1 )
    {
        mStrategyGraph.push_back( new Vertex() );
    }

    StrategyGraph::~StrategyGraph()
    {
        while( !mStrategyGraph.empty() )
        {
            Vertex* toBeDeleted = mStrategyGraph.back();
            mStrategyGraph.pop_back();
            delete toBeDeleted;
        }
    }

    void StrategyGraph::addCondition( size_t _from, size_t _to, ConditionEvaluation _conditionEvaluation )
    {
        assert( _from<mStrategyGraph.size() );
        assert( _to<mStrategyGraph.size() );
        assert( _from!=_to );

        // New branch or backlink
        if( _from<(mStrategyGraph.size()-2) || _to<_from )
        {
            mNumberOfBranches++;
        }
        mStrategyGraph[ _from ]->addSuccessorVertex( _to, _conditionEvaluation );
    }

    size_t StrategyGraph::setThreadIds( size_t _from, size_t _threadId )
    {
        size_t threadId = _threadId;
        vector<Edge>& edges = mStrategyGraph[ _from ]->edgeList();
        if( edges.size()!=0 )
        {
            for( auto edge = edges.rbegin(); edge!=edges.rend(); )
            {
                edge->setThreadId( threadId );

                // Backend
                if( edge->successorVertex()>_from )
                {
                    threadId = setThreadIds( edge->successorVertex(), threadId );
                }
                // Backlink
                else
                {
                    edge->setThreadId( --threadId );
                }

                ++edge;
                if( edge!=edges.rend() )
                {
                    --threadId;
                }
            }
        }
        return threadId;
    }

    size_t StrategyGraph::addBackend( size_t _at, ModuleType _moduleType, ConditionEvaluation _conditionEvaluation )
    {
        mStrategyGraph.push_back( new Vertex( _moduleType ) );
        addCondition( _at, mStrategyGraph.size()-1, _conditionEvaluation );
        return mStrategyGraph.size()-1;
    }

    void StrategyGraph::addBacklink( size_t _from, size_t _to, ConditionEvaluation _conditionEvaluation )
    {
        addCondition( _from, _to, _conditionEvaluation );
    }

    // Returns module types ordered by priority, highest priority (lowest value) first
    vector< pair< thread_priority, ModuleType > > StrategyGraph::getNextModuleTypes( size_t _from, carl::Condition _condition )
    {
        vector< pair< thread_priority, ModuleType > > result = vector< pair< thread_priority, ModuleType > >();
        const vector<Edge>& edges = mStrategyGraph[ _from ]->edgeList();
        for( auto edge = edges.begin(); edge!=edges.end(); ++edge )
        {
            if ( edge->conditionEvaluation()( _condition ) )
            {
                thread_priority threadPriority = thread_priority( edge->threadId(), edge->priority() );
                result.push_back( pair< thread_priority, ModuleType >( threadPriority, mStrategyGraph[ edge->successorVertex() ]->moduleType() ) );
            }
        }
        return result;
    }
}    // namespace smtrat