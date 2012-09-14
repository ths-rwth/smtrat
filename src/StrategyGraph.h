/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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


/**
 * @file StrategyGraph.h
 *
 * @author Henrik Schmitz
 * @since 2012-09-10
 * @version 2012-09-10
 */

#ifndef SMTRAT_STRATEGYGRAPH_H
#define SMTRAT_STRATEGYGRAPH_H

#include <vector>

#include "Formula.h"
#include "ModuleType.h"

namespace smtrat
{
    ///////////
    // Types //
    ///////////

    typedef bool (*ConditionEvaluation)( Condition );
    static bool isCondition( Condition _condition )
    {
        return true;
    }
    
//    static bool isConjunction( Condition _condition )
//    {
//        return PROP_IS_PURE_CONJUNCTION <= _condition;
//    }
    
    /**
     *
     */
    class StrategyGraph
    {
        private:
            
            class Edge;
            
            class Vertex
            {
                private:
                    ModuleType mModuleType;
                    std::vector<Edge>* mpEdgeList;
                    
                    bool successorExists( unsigned ) const;
                
                public:
                    Vertex();
                    Vertex( ModuleType );
                    ~Vertex();
                    
                    void addSuccessor( unsigned, ConditionEvaluation );
                    
                    const ModuleType& moduleType() const
                    {
                        return mModuleType;
                    };
                    
                    const std::vector<Edge>& edgeList() const 
                    {
                        return *mpEdgeList;
                    };

//                    std::vector<Edge>& rEdgeList()
//                    {
//                        return *mpEdgeList;
//                    };
            };
            
            class Edge
            {
                private:
                    unsigned mSuccessor;
                    ConditionEvaluation mpCondition;
                    
                public:
                    Edge();
                    Edge( unsigned, ConditionEvaluation );
                    ~Edge();
                    
                    const unsigned successor() const
                    {
                        return mSuccessor;
                    };
                    
                    const ConditionEvaluation conditionEvaluation() const
                    {
                        return *mpCondition;
                    }
                    
                    
            };
            
            // members
            
            std::vector<Vertex> mStrategyGraph;
//            unsigned mIndexAllocator;

        public:
            // [Con|De]structors

            /**
             * Standard strategy which is an empty strategy.
             */
            StrategyGraph();

            /**
             * Standard destructor.
             */
            ~StrategyGraph();
            
            // Accessors
            
            // Methods

            unsigned addSuccessor( unsigned, ModuleType, ConditionEvaluation = isCondition );
            
            void addEdge( unsigned, unsigned, ConditionEvaluation = isCondition );
            
            std::vector< std::pair<unsigned, ModuleType> > nextModuleTypes( unsigned, Condition );
    };
}    // namespace smtrat

#endif   /* SMTRAT_STRATEGYGRAPH_H */
