/** 
 * @file   VariableConstraintGraph.h
 *         Created on January 17, 2013, 11:15 PM
 * @author: Sebastian Junges
 *
 * 
 */

#ifndef VARIABLECONSTRAINTGRAPH_H
#define	VARIABLECONSTRAINTGRAPH_H

namespace smtrat 
{

    struct VariableNode
    {
        std::list<ConstraintNode*> adjacencyList;
    };

    struct ConstraintNode 
    {
        Constraint* constraint;
        Formula::const_iterator posInPassedFormula;
        std::list<VariableNode*> adjacencyList;
    };

    class VariableConstraintGraph
    {
    protected:
        std::vector<VariableNode*> variableNodes;
        std::vector<ConstraintNode*> 
    public:
        VariableConstraintGraph( );
        virtual ~VariableConstraintGraph( ) {}
    private:

    };
}

#endif	/* VARIABLECONSTRAINTGRAPH_H */

