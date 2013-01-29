/** 
 * @file   VariableConstraintGraph.h
 *         Created on January 17, 2013, 11:15 PM
 * @author: Sebastian Junges
 *
 * 
 */

#pragma once

#include <list>
#include <vector>
#include "Formula.h"
#include <map>

namespace smtrat 
{

    struct ConstraintNode;
    struct VariableNode
    {
        // Constraintid -> ConstraintNode
        std::map<unsigned,ConstraintNode*> adjacencyList;
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
        /// identifier -> node
        std::map<std::string,VariableNode*> variableNodes;
        std::list<ConstraintNode*> constraintNodes;
    public:
        VariableConstraintGraph( );
        std::list<ConstraintNode*>::iterator addConstraint(Constraint* constraint, Formula::const_iterator pos);
        bool removeConstraint(std::list<ConstraintNode*>::iterator);
        
        void print(); 
        virtual ~VariableConstraintGraph( ) {}
    private:

    };
}
