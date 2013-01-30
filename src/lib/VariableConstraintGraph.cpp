/** 
 * @file   VariableConstraintGraph.cpp
 *         Created on January 17, 2013, 11:15 PM
 * @author: Sebastian Junges
 *
 * 
 */


#include "VariableConstraintGraph.h"
#include "Answer.h"

namespace smtrat 
{
    VariableConstraintGraph::VariableConstraintGraph( )
    {
    }
    
    std::list<ConstraintNode*> VariableConstraintGraph::addConstraint(const Constraint* constraint, Formula::const_iterator origin, Formula::iterator pos) 
    {
        std::list<ConstraintNode*> readd;
        mConstraintNodes.push_back(new ConstraintNode());
        (mConstraintNodes.back())->constraint = constraint;
        (mConstraintNodes.back())->posInPassedFormula = pos;
        (mConstraintNodes.back())->posInReceivedFormula = origin;
        // We assume that the variables in the symtab are exact.
        for( GiNaC::symtab::const_iterator itVar = constraint->variables().begin(); itVar != constraint->variables().end(); ++itVar )
        {
            // Search for the variable node corresponding to the current variable.
            std::map<std::string, VariableNode*>::const_iterator itVarNode = mVariableNodes.find(itVar->first);
            // Check whether such a node already exists. If not, create one.
            if(itVarNode == mVariableNodes.end()) 
            {
                itVarNode = mVariableNodes.insert(std::pair<std::string, VariableNode*>(itVar->first, new VariableNode(itVar->second))).first;
            }
            else 
            {
                std::set<VariableNode*>::iterator singleVarEntry = mSingleAppearingVariables.find(itVarNode->second);
                if(singleVarEntry != mSingleAppearingVariables.end()) 
                {
                    mSingleAppearingVariables.erase(singleVarEntry);
                    assert(itVarNode->second->adjacencyList.size() == 1);
                    readd.push_back(itVarNode->second->adjacencyList.begin()->second);
                }
            }
                
            // Add the current constraint to the adjacencylist.
            itVarNode->second->adjacencyList.insert(std::pair<unsigned, ConstraintNode*>(constraint->id(), mConstraintNodes.back()));
            // Add the variable to this constraints adjacencylist
            mConstraintNodes.back()->adjacencyList.push_back(itVarNode->second);
        }
        return readd;        
    }
    
    std::list<ConstraintNode*> VariableConstraintGraph::updateConstraintNode(ConstraintNode* node, Formula::iterator pos) 
    {
        std::list<ConstraintNode*> readd;
        node->posInPassedFormula = pos;
        node->adjacencyList.clear();
        // We assume that the variables in the symtab are exact.
        for( GiNaC::symtab::const_iterator itVar = node->constraint->variables().begin(); itVar != node->constraint->variables().end(); ++itVar )
        {
            // As this is an update, we can be sure the variables already exist.
            std::map<std::string, VariableNode*>::const_iterator itVarNode = mVariableNodes.find(itVar->first);
            assert(itVarNode != mVariableNodes.end());
            std::set<VariableNode*>::iterator singleVarEntry = mSingleAppearingVariables.find(itVarNode->second);
            if(singleVarEntry != mSingleAppearingVariables.end()) 
            {
                mSingleAppearingVariables.erase(singleVarEntry);
                assert(itVarNode->second->adjacencyList.size() == 1);
                readd.push_back(itVarNode->second->adjacencyList.begin()->second);
            }

            // Add the current constraint to the adjacencylist.
            itVarNode->second->adjacencyList.insert(std::pair<unsigned, ConstraintNode*>(node->constraint->id(), node));
            // Add the variable to this constraints adjacencylist
            node->adjacencyList.push_back(itVarNode->second);
        }
        return readd;        
    }
    
    bool VariableConstraintGraph::removeConstraint(std::list<ConstraintNode*>::iterator constraintNode , Formula::const_iterator end )
    {
        bool nothingChanges = false;
        // If constraint is already not passed
        if( (*constraintNode)->posInPassedFormula ==  end) 
        {
            nothingChanges = true;
            assert( (*constraintNode)->adjacencyList.size() == 1);
            mSingleAppearingVariables.erase( (*constraintNode)->adjacencyList.front() );
        }
        
        // Remove all the links from the variable to the node
        for(std::list<VariableNode*>::iterator itVar = (*constraintNode)->adjacencyList.begin(); itVar != (*constraintNode)->adjacencyList.end(); ++itVar)
        {
            // Remove the constraint 
            (*itVar)->adjacencyList.erase((*constraintNode)->constraint->id());
        }
        
        // Remove the constraintnode
        delete *constraintNode;
        // Remove the entry
        mConstraintNodes.erase(constraintNode);
        return !nothingChanges;
    }
                
    std::list<const Constraint*> VariableConstraintGraph::restoreRelevantConstraints() {
        for(std::set<VariableNode*>::iterator itVar = mSingleAppearingVariables.begin(); itVar != mSingleAppearingVariables.end(); ++itVar) {
            if( (*itVar)->adjacencyList.size() > 1) 
            {
                
            }
                
        }

    }
    
    std::list<Formula::iterator> VariableConstraintGraph::findIrrelevantConstraints(Formula::iterator end)
    {
        std::list<Formula::iterator> irrelevantConstraints;
        for(std::map<std::string, VariableNode*>::const_iterator itVar = mVariableNodes.begin(); itVar != mVariableNodes.end(); ++itVar)
        {
            VariableNode* varNode = itVar->second;
            if( varNode->adjacencyList.size() == 1 )
            {
                ConstraintNode* constraintNode = varNode->adjacencyList.begin()->second;
                if(constraintNode->posInPassedFormula == end) continue;
                VarInfo varInfo(constraintNode->constraint->varInfo(varNode->variable));
                // the variable should occur only once and with an odd degree.
                if( varInfo.occurences == 1 && varInfo.maxDegree%2 == 1)
                {
                    // as the variable occurs only once the max and mindegree are assumed to be equal.
                    assert(varInfo.maxDegree == varInfo.minDegree);
                    irrelevantConstraints.push_back(constraintNode->posInPassedFormula);
                    constraintNode->posInPassedFormula = end;
                    
                    // Remove all the links from the variable to the node
                    for(std::list<VariableNode*>::iterator itOtherVar = (constraintNode)->adjacencyList.begin(); itOtherVar != (constraintNode)->adjacencyList.end(); ++itOtherVar)
                    {
                        // Remove the constraint from all other variables, but not from this one!
                       (*itOtherVar)->adjacencyList.erase( (constraintNode)->constraint->id() );
                       
                    }
                    varNode->adjacencyList.insert(std::pair<unsigned, ConstraintNode*>(constraintNode->constraint->id(), constraintNode));
                    // Remove all the links from the constraintnode to all variables
                    constraintNode->adjacencyList.clear();
                    // And add the current variable node again.
                    constraintNode->adjacencyList.push_back(varNode);
                    
                    // Now we remember this variable as being treated.
                    mSingleAppearingVariables.insert(  itVar->second );
                }
                
            }
        }
        return irrelevantConstraints;
    }
    
    void VariableConstraintGraph::print() 
    {
        std::cout << "Constraint nodes:" << std::endl;
        for( std::list<ConstraintNode*>::const_iterator it = mConstraintNodes.begin(); it != mConstraintNodes.end(); ++it ) 
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
        for( std::map<std::string, VariableNode*>::const_iterator itVarNode = mVariableNodes.begin(); itVarNode != mVariableNodes.end(); ++itVarNode )
        {
            std::cout << "\tVariable: " << itVarNode->first << " (" << itVarNode->second << ")" << std::endl;
            std::cout << "\tConstraints (by id): " << std::endl;
            for( std::map<unsigned, ConstraintNode*>::const_iterator itConstraints = itVarNode->second->adjacencyList.begin();  itConstraints != itVarNode->second->adjacencyList.end(); ++itConstraints)
            {
                std::cout << "\t\t" << itConstraints->first << " (" << itConstraints->second->constraint->lhs() << ")" << std::endl;
            }
        }
        
    }
}


