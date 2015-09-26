/**
 * @file StrategyGraph.h
 *
 * @author  Henrik Schmitz
 * @since   2012-09-10
 * @version 2013-01-31
 */

#pragma once

#include <vector>

#include "../Common.h"
#include "ThreadPool.h"
#include "../modules/ModuleType.h"

namespace smtrat
{
    typedef bool (*ConditionEvaluation)( carl::Condition );

    bool isCondition( carl::Condition _condition );

    class StrategyGraph
    {
        private:
            class Edge
            {
                private:
                    size_t mSuccessorVertex;
                    size_t mThreadId;
                    size_t mPriority;
                    ConditionEvaluation mpConditionEvaluation;

                public:
                    Edge( size_t _to, ConditionEvaluation _conditionEvaluation, size_t _priority ):
                        mSuccessorVertex( _to ),
                        mThreadId( 0 ),
                        mPriority( _priority ),
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

                    void addSuccessorVertex( size_t _to, ConditionEvaluation _conditionEvaluation, size_t _priority )
                    {
                        assert( !successorVertexExists( _to ) );
                        mpEdgeList->push_back( Edge( _to, _conditionEvaluation, _priority ) );
                    }
            };

            std::vector<Vertex*> mStrategyGraph;
            size_t mNumberOfBranches;
            size_t mPriorityAllocator;

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
            std::vector< std::pair< thread_priority, ModuleType > > getNextModuleTypes( size_t, carl::Condition );

// To be deleted
//            void tmpPrint();
    };
}    // namespace smtrat

