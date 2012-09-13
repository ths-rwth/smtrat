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


/**    // namespace smtrat
 * @file StrategyGraph.h
 *
 * @author Henrik Schmitz
 * @since 2012-09-10
 * @version 2012-09-10
 */

#ifndef SMTRAT_STRATEGYGRAPH_H
#define SMTRAT_STRATEGYGRAPH_H

#include <vector>

namespace smtrat
{
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
                    int Modul;
                    std::vector<Edge> mEdgeList;
            };
            
            class Edge
            {
                private:
                    int Condition;
                    Vertex* pSuccessor;
            };

            // members

        public:
            // [Con|De]structors

            /**
             * Standard strategy which is an empty strategy.
             */
            StrategyGraph();

            /**
             * Copy constructor.
             */
            StrategyGraph( const StrategyGraph& );

            /**
             * Standard destructor.
             */
            ~StrategyGraph();
            
            // Accessors   

    };
}    // namespace smtrat

#endif   /* SMTRAT_STRATEGYGRAPH_H */
