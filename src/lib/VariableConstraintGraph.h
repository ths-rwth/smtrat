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
        Formula::const_iterator posInReceivedFormula;
        Formula::iterator posInPassedFormula;
        std::list<VariableNode*> adjacencyList;
    };

    class VariableConstraintGraph
    {
    protected:
        /// identifier -> node
        std::map<std::string,VariableNode*> mVariableNodes;
        std::list<ConstraintNode*> mConstraintNodes;
        std::set<VariableNode*> mSingleAppearingVariables;
        
    public:
        VariableConstraintGraph( );
        std::list<ConstraintNode*> addConstraint(const Constraint* constraint,Formula::const_iterator origin, Formula::iterator pos);
        std::list<ConstraintNode*> updateConstraintNode(ConstraintNode* node, Formula::iterator pos);
        bool removeConstraint(std::list<ConstraintNode*>::iterator, Formula::const_iterator end);
        
        std::list<ConstraintNode*>::iterator last()  { return --mConstraintNodes.end(); }
        
        std::list<const Constraint*> restoreRelevantConstraints();
        std::list<Formula::iterator> findIrrelevantConstraints(Formula::iterator end);
        
        void print(); 
        virtual ~VariableConstraintGraph( ) {}
    private:

    };
}
