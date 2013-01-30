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
        VariableNode();
        VariableNode(const GiNaC::ex& var) : variable(var) {}; 
        
        // Constraintid -> ConstraintNode
        std::map<unsigned,ConstraintNode*> adjacencyList;
        GiNaC::ex variable;
    };

    struct ConstraintNode 
    {
        const Constraint* constraint;
        Formula::const_iterator posInPassedFormula;
        std::list<VariableNode*> adjacencyList;
    };

    class VariableConstraintGraph
    {
    protected:
        /// identifier -> node
        std::map<std::string,VariableNode*> mVariableNodes;
        std::list<ConstraintNode*> mConstraintNodes;
    public:
        VariableConstraintGraph( );
        std::list<ConstraintNode*>::iterator addConstraint(const Constraint* constraint, Formula::const_iterator pos);
        bool removeConstraint(std::list<ConstraintNode*>::iterator);
        
        std::list<Formula::const_iterator> findIrrelevantConstraints(Formula::const_iterator end);
        
        void print(); 
        virtual ~VariableConstraintGraph( ) {}
    private:

    };
}
