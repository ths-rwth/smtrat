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


 /* @file StrategyGraph.cpp
 *
 * @author Henrik Schmitz
 * @since 2012-09-10
 * @version 2012-09-10
 */

#include "StrategyGraph.h"

using namespace std;

namespace smtrat{
    ///////////////
    // Functions //
    ///////////////
    
    StrategyGraph::Edge::Edge(){}
    
    StrategyGraph::Edge::Edge( unsigned to, ConditionEvaluation condition ):
        mSuccessor( to ),
        mpCondition( condition )
    {}
    
    StrategyGraph::Edge::~Edge(){}


    StrategyGraph::Vertex::Vertex():
        mModuleType( MT_Module ),
        mpEdgeList( new vector<Edge>() )
    {}

    StrategyGraph::Vertex::Vertex( ModuleType moduleType ):
        mModuleType( moduleType ),
        mpEdgeList( new vector<Edge>() )
    {}
    
    StrategyGraph::Vertex::~Vertex(){}
    

    StrategyGraph::StrategyGraph():
        mStrategyGraph()
    {
        mStrategyGraph.push_back( Vertex() );
    }

    StrategyGraph::~StrategyGraph(){}

    ///////////////
    // Functions //
    ///////////////
   
    /**
     * ...
     *
     * @param formula       The formula to be considered.
     *
     * @return void
     */
    unsigned StrategyGraph::addSuccessor( unsigned at, ModuleType moduleType, ConditionEvaluation condition )
    {
        Vertex vertexInsert = Vertex( moduleType );
        mStrategyGraph.push_back( vertexInsert );
        
        addEdge( at, mStrategyGraph.size()-1, condition );
        
        return mStrategyGraph.size()-1;
    }
    
    bool StrategyGraph::Vertex::successorExists( unsigned to ) const
    {
        for(auto edge = mpEdgeList->begin(); edge!=mpEdgeList->end(); ++edge) {
            if (edge->successor()==to)
                return true;
        }
        return false;
    }
    
    void StrategyGraph::Vertex::addSuccessor( unsigned to, ConditionEvaluation condition )
    {
        assert(!successorExists(to));
        mpEdgeList->push_back( Edge( to, condition ) );
    }
    
    /**
     * ...
     *
     * @param formula       The formula to be considered.
     *
     * @return void
     */
    void StrategyGraph::addEdge( unsigned from, unsigned to, ConditionEvaluation condition )
    {
        mStrategyGraph[from].addSuccessor( to, condition );
    }
    
    /**
     * ...
     *
     * @param formula       The formula to be considered.
     *
     * @return void
     */
    vector< pair<unsigned, ModuleType> > StrategyGraph::nextModuleTypes( unsigned from, Condition condition )
    {
        vector< pair<unsigned, ModuleType> > result = vector< pair<unsigned, ModuleType> >();
        
        const vector<Edge>& edges = mStrategyGraph[from].edgeList();
        for(auto edge = edges.begin(); edge!=edges.end(); ++edge){
            if (edge->conditionEvaluation()( condition ))
            {
                unsigned succ = edge->successor();
                result.push_back( pair<unsigned, ModuleType>( succ, mStrategyGraph[succ].moduleType() ) );
            }
        }
        return result;
    }

}    // namespace smtrat