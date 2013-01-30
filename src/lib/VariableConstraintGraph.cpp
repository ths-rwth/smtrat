/** 
 * @file   VariableConstraintGraph.cpp
 *         Created on January 17, 2013, 11:15 PM
 * @author: Sebastian Junges
 *
 * 
 */


#include "VariableConstraintGraph.h"

namespace smtrat 
{
    VariableConstraintGraph::VariableConstraintGraph( )
    {
    }
    
    std::list<ConstraintNode*>::iterator VariableConstraintGraph::addConstraint(const Constraint* constraint, Formula::const_iterator pos) 
    {
        constraintNodes.push_back(new ConstraintNode());
        (constraintNodes.back())->constraint = constraint;
        (constraintNodes.back())->posInPassedFormula = pos;
        // We assume that the variables in the symtab are exact.
        for( GiNaC::symtab::const_iterator itVar = constraint->variables().begin(); itVar != constraint->variables().end(); ++itVar )
        {
            // Search for the variable node corresponding to the current variable.
            std::map<std::string, VariableNode*>::const_iterator itVarNode = variableNodes.find(itVar->first);
            // Check whether such a node already exists. If not, create one.
            if(itVarNode == variableNodes.end()) 
            {
                itVarNode = variableNodes.insert(std::pair<std::string, VariableNode*>(itVar->first, new VariableNode())).first;
            }
            // Add the current constraint to the adjacencylist.
            itVarNode->second->adjacencyList.insert(std::pair<unsigned, ConstraintNode*>(constraint->id(), constraintNodes.back()));
            // Add the variable to this constraints adjacencylist
            constraintNodes.back()->adjacencyList.push_back(itVarNode->second);
        }
        
        return --constraintNodes.end();
        
    }
    
    bool VariableConstraintGraph::removeConstraint(std::list<ConstraintNode*>::iterator constraintNode)
    {
        
        // Remove all the links from the variable to the node
        for(std::list<VariableNode*>::iterator itVar = (*constraintNode)->adjacencyList.begin(); itVar != (*constraintNode)->adjacencyList.end(); ++itVar)
        {
            // Remove the constraint 
            (*itVar)->adjacencyList.erase((*constraintNode)->constraint->id());
        }
        // Remove the constraintnode
        delete *constraintNode;
        // Remove the entry
        constraintNodes.erase(constraintNode);
        return true;
    }
    
    void VariableConstraintGraph::print() 
    {
        std::cout << "Constraint nodes:" << std::endl;
        for( std::list<ConstraintNode*>::const_iterator it = constraintNodes.begin(); it != constraintNodes.end(); ++it ) 
        {
            std::cout << "\tConstraint: ";
            (*it)->constraint->print();
            std::cout << "(" << (*it)->constraint->id() << ")" << std::endl;
            std::cout << "\tVariable nodes:" << std::endl;
            for( std::list<VariableNode*>::const_iterator itVarNode = (*it)->adjacencyList.begin(); itVarNode != (*it)->adjacencyList.end(); ++itVarNode )
            {
                std::cout << "\t\t" << *itVarNode << std::endl;
            }    
        }
        std::cout << "Variable nodes:" << std::endl;
        for( std::map<std::string, VariableNode*>::const_iterator itVarNode = variableNodes.begin(); itVarNode != variableNodes.end(); ++itVarNode )
        {
            std::cout << "\tVariable: " << itVarNode->first << " (" << itVarNode->second << ")" << std::endl;
            std::cout << "\tConstraints (by id): " << std::endl;
            for( std::map<unsigned, ConstraintNode*>::const_iterator itConstraints = itVarNode->second->adjacencyList.begin();  itConstraints != itVarNode->second->adjacencyList.end(); ++itConstraints)
            {
                std::cout << "\t\t" << itConstraints->first << std::endl;
            }
        }
        
    }
}


