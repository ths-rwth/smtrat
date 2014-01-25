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
 * @file StrategyGraph.h
 *
 * @author  Henrik Schmitz
 * @since   2012-09-10
 * @version 2013-01-31
 */

#ifndef SMTRAT_STRATEGYGRAPH_H
#define SMTRAT_STRATEGYGRAPH_H

#include <vector>

#include "Formula.h"
#include "ThreadPool.h"
#include "modules/ModuleType.h"

namespace smtrat
{
    typedef bool (*ConditionEvaluation)( Condition );

    static inline bool isCondition( Condition _condition )
    {
        return PROP_TRUE <= _condition;
    }

    class StrategyGraph
    {
        private:
            class Edge
            {
                private:
                    static size_t mPriorityAllocator;
                    size_t mSuccessorVertex;
                    size_t mThreadId;
                    size_t mPriority;
                    ConditionEvaluation mpConditionEvaluation;

                public:
                    Edge( size_t _to, ConditionEvaluation _conditionEvaluation ):
                        mSuccessorVertex( _to ),
                        mPriority( mPriorityAllocator++ ),
                        mpConditionEvaluation( _conditionEvaluation )
                    {}

                    ~Edge(){}

                    size_t successorVertex() const
                    {
                        return mSuccessorVertex;
                    }

                    size_t threadId() const
                    {
                        return mThreadId;
                    }

                    void setThreadId( size_t _threadId )
                    {
                        mThreadId = _threadId;
                    }

                    size_t priority() const
                    {
                        return mPriority;
                    }

                    ConditionEvaluation conditionEvaluation() const
                    {
                        return *mpConditionEvaluation;
                    }
            };

            class Vertex
            {
                private:
                    std::vector<Edge>* mpEdgeList;
                    ModuleType mModuleType;

                    bool successorVertexExists( size_t _to ) const
                    {
                        for( auto edge = mpEdgeList->begin(); edge!=mpEdgeList->end(); ++edge )
                        {
                            if ( edge->successorVertex() == _to )
                            {
                                return true;
                            }
                        }
                        return false;
                    }

                public:
                    Vertex():
                        mpEdgeList( new std::vector<Edge>() ),
                        mModuleType( MT_Module )
                    {}

                    Vertex( ModuleType _moduleType ):
                        mpEdgeList( new std::vector<Edge>() ),
                        mModuleType( _moduleType )
                    {}

                    ~Vertex()
                    {
                        delete mpEdgeList;
                    }

                    std::vector<Edge>& edgeList() const
                    {
                        return *mpEdgeList;
                    }

                    const ModuleType& moduleType() const
                    {
                        return mModuleType;
                    }

                    void addSuccessorVertex( size_t _to, ConditionEvaluation _conditionEvaluation )
                    {
                        assert( !successorVertexExists( _to ) );
                        mpEdgeList->push_back( Edge( _to, _conditionEvaluation ) );
                    }
            };

            std::vector<Vertex*> mStrategyGraph;
            size_t mNumberOfBranches;

            void addCondition( size_t, size_t, ConditionEvaluation );
            size_t setThreadIds( size_t, size_t );

        public:
            StrategyGraph();
            ~StrategyGraph();

            size_t numberOfBranches() const
            {
                return mNumberOfBranches;
            }

            void setThreadAndBranchIds()
            {
                setThreadIds( 0, (numberOfBranches()-1) );
            }

            // Backends and back links must be added by priority, i.e. starting with highest priority (lowest value)
            size_t addBackend( size_t, ModuleType, ConditionEvaluation = isCondition );
            void addBacklink( size_t, size_t, ConditionEvaluation = isCondition );
            std::vector< std::pair< thread_priority, ModuleType > > getNextModuleTypes( size_t, Condition );

// To be deleted
//            void tmpPrint();
    };
}    // namespace smtrat

#endif   /* SMTRAT_STRATEGYGRAPH_H */
