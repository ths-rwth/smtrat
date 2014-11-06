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
#include "../../Common.h"
#include <map>

namespace smtrat 
{
/**
 * A namespace for the V(ariable)R(ewrite)M(odule)
 */
namespace vrw 
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
        const ConstraintT* constraint;
        FormulaT::const_iterator posInReceivedFormula;
        FormulaT::iterator posInPassedFormula;
        std::list<VariableNode*> adjacencyList;
        bool unasserted;
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
        std::list<ConstraintNode*> addConstraint(const ConstraintT* constraint,FormulaT::const_iterator origin, FormulaT::iterator pos);
        std::list<ConstraintNode*> updateConstraintNode(ConstraintNode* node, FormulaT::iterator pos);
        bool removeConstraint(std::list<ConstraintNode*>::iterator, FormulaT::const_iterator end);
        void assertConstraints();
        
        
        std::list<ConstraintNode*>::iterator last()  { return --mConstraintNodes.end(); }
        
        std::list<std::pair<FormulaT::iterator, bool> > findIrrelevantConstraints(FormulaT::iterator end);
        std::list<std::pair<FormulaT::iterator, bool> > findPurelyLinearComponents(FormulaT::iterator end);
        void print(); 
        virtual ~VariableConstraintGraph( ) {}
    private:

    };

}
}

