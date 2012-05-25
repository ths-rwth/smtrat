/* SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.MutableTreeNode;

/**
 *
 * @author Ulrich Loup
 * @since 2012-02-07
 * @version 2012-03-09
 */
class Strategy extends DefaultMutableTreeNode
{
    /// anchor of a strategy definition line
    private static final String STRATEGY_DEFINITION_ANCHOR = "STRATEGYDEFINITION";
    /// template of a solver name
    private static final String STRATEGY_SOLVERNAME = "MySolver";
    /// template of a solver header file
    private static final String STRATEGY_HEADER = "/*\r\n * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox\r\n * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges\r\n *\r\n * This file is part of SMT-RAT.\r\n *\r\n * SMT-RAT is free software: you can redistribute it and/or modify\r\n * it under the terms of the GNU General Public License as published by\r\n * the Free Software Foundation, either version 3 of the License, or\r\n * (at your option) any later version.\r\n *\r\n * SMT-RAT is distributed in the hope that it will be useful,\r\n * but WITHOUT ANY WARRANTY; without even the implied warranty of\r\n * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\r\n * GNU General Public License for more details.\r\n *\r\n * You should have received a copy of the GNU General Public License\r\n * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.\r\n *\r\n */\r\n\r\n\r\n/**\r\n * @file " + STRATEGY_SOLVERNAME + ".h\r\n *\r\n */\r\n#ifndef SMTRAT_" + STRATEGY_SOLVERNAME.toUpperCase() + "_H\r\n#define SMTRAT_" + STRATEGY_SOLVERNAME.toUpperCase() + "_H\r\n\r\n#include \"Manager.h\"\r\n\r\nnamespace smtrat\r\n{\r\n/**\r\n * Strategy description.\r\n *\r\n * @author \r\n * @since \r\n * @version \r\n *\r\n */\r\nclass " + STRATEGY_SOLVERNAME + ": public Manager\r\n{\r\npublic:\r\n    " + STRATEGY_SOLVERNAME + "( );\r\n    ~" + STRATEGY_SOLVERNAME + "();\r\n\n};\r\n\n} // namespace smtrat\r\n#endif   /** SMTRAT_" + STRATEGY_SOLVERNAME.toUpperCase() + "_H */\r\n";
    /// template of a solver implementation file
    private static final String STRATEGY_IMPLEMENTATION = "/*\r\n * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox\r\n * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges\r\n *\r\n * This file is part of SMT-RAT.\r\n *\r\n * SMT-RAT is free software: you can redistribute it and/or modify\r\n * it under the terms of the GNU General Public License as published by\r\n * the Free Software Foundation, either version 3 of the License, or\r\n * (at your option) any later version.\r\n *\r\n * SMT-RAT is distributed in the hope that it will be useful,\r\n * but WITHOUT ANY WARRANTY; without even the implied warranty of\r\n * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\r\n * GNU General Public License for more details.\r\n *\r\n * You should have received a copy of the GNU General Public License\r\n * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.\r\n *\r\n */\r\n\r\n\r\n/**\r\n * @file " + STRATEGY_SOLVERNAME + ".cpp\r\n *\r\n */\r\n\r\n#include \"" + STRATEGY_SOLVERNAME + ".h\"\r\n\r\nnamespace smtrat\r\n{\r\n    " + STRATEGY_SOLVERNAME + "::" + STRATEGY_SOLVERNAME + "( ) : Manager( )\r\n    {" + STRATEGY_DEFINITION_ANCHOR + "\r\n    }\r\n\n    " + STRATEGY_SOLVERNAME + "::~" + STRATEGY_SOLVERNAME + "() {}\r\n\n}    // namespace smtrat\r\n";
    /// template of a strategy definition line
    private static final String STRATEGY_DEFINITION = "\r\n        strategy().addModuleType( PROPERTY, MODULE );";
    /// template of a strategy definition line
    private static final String STRATEGY_TRUE_CONDITION = "PROP_TRUE";
    /// if true, the node represents a condition, otherwise a module
    private boolean isCondition;

    //////////////////
    // CONSTRUCTORS //
    //////////////////
    /**
     * Constructs a node which is either a module node or a condition node determined by the flag isCondition.
     *
     * @param name
     * @param isCondition if true, the node represents a condition, otherwise a module
     */
    public Strategy( String name, boolean isCondition )
    {
        super( name );
        this.isCondition = isCondition;
    }

    /**
     * Constructs a node which is a condition node setting isCondition to true.
     *
     * @param condition
     */
    public Strategy( String condition )
    {
        super( condition );
        this.isCondition = true;
    }

    /**
     * Constructs a node which is a module node setting isCondition to false.
     *
     * @param module
     */
    public Strategy( Module module )
    {
        super( module.type() );
        this.isCondition = false;
    }

    /**
     * Constructs a node which is a condition node, setting isCondition to true, and has already one module as child.
     *
     * @param condition
     * @param module
     */
    public Strategy( String condition, String module )
    {
        super( condition );
        super.add( new Strategy( module, false ) );
        this.isCondition = true;
    }

    ///////////////
    // SELECTORS //
    ///////////////
    /**
     * @return true, if the node represents a condition, otherwise it represents a module
     */
    public boolean isCondition()
    {
        return this.isCondition;
    }

    /////////////////////
    // CODE GENERATION //
    /////////////////////
    /**
     * Generate the contents of a header file implementing the solver given by the specified name.
     *
     * @return string representing the contents of a header file implementing the solver given by the specified name
     */
    public String generateHeader( String name )
    {
        return STRATEGY_HEADER.replaceAll( STRATEGY_SOLVERNAME, name ).replaceAll( STRATEGY_SOLVERNAME.toUpperCase(), name.toUpperCase() );
    }

    /**
     * Generate the contents of a cpp file implementing this strategy with the given solver name.
     *
     * The strategy is interpreted as follows: <ul> <li>All children of this node of type condition are added in the order of their occurrence in the
     * children list.</li> <li>If there is no condition child, take the first module child with the property STRATEGY_TRUE_CONDITION.</li> </ul>
     *
     * @return string representing the contents of a cpp file implementing this strategy with the given solver name
     */
    public String generateImplementation( String name )
    {
        // prepare the strategy string
        String strategyString = "";
        for( Object conditionObj : super.children )
        {
            Strategy condition = (Strategy) conditionObj;
            if( condition.isCondition )
                for( Object moduleObj : condition.children )
                {
                    Strategy module = (Strategy) moduleObj;
                    strategyString += STRATEGY_DEFINITION.replaceAll( "MODULE", module.getUserObject().toString() ).replaceAll( "PROPERTY", condition.getUserObject().toString() );
                }
        }
        if( strategyString.isEmpty() && !super.children.isEmpty() ) // no condition child found, but module child exists
            strategyString += STRATEGY_DEFINITION.replaceAll( "MODULE", ((Strategy) super.children.firstElement()).getUserObject().toString() ).replaceAll( "PROPERTY", STRATEGY_TRUE_CONDITION );
        // put everything together
        return STRATEGY_IMPLEMENTATION.replaceAll( STRATEGY_SOLVERNAME, name ).replaceAll( STRATEGY_SOLVERNAME.toUpperCase(), name.toUpperCase() ).replaceAll( STRATEGY_DEFINITION_ANCHOR, strategyString );
    }

    /////////////////
    // DATA ACCESS //
    /////////////////
    /**
     * Get the first child if available, otherwise return null.
     *
     * @return first child if available, otherwise null
     */
    public Strategy getFirstChild()
    {
        if( super.isLeaf() )
            return null;
        return (Strategy) super.getFirstChild();
    }

    /**
     * Add a new child to the strategy node.
     *
     * @param newChild
     */
    public void add( MutableTreeNode newChild )
    {
        super.add( newChild );
    }

    /**
     * Add a new child to the strategy node, inserting it after the first occurrence of existingChild.
     *
     * @param newChild
     * @param existingChild
     */
    public void addAfter( Strategy newChild, Strategy existingChild )
    {
        super.insert( newChild, super.getIndex( existingChild ) + 1 );
    }

    /**
     * Add a new child to the strategy node, inserting it before the first occurrence of existingChild.
     *
     * @param newChild
     * @param existingChild
     */
    public void addBefore( Strategy newChild, Strategy existingChild )
    {
        super.insert( newChild, super.getIndex( existingChild ) );
    }

    /**
     * Add a new child to the strategy node, adding it as last child of the first occurrence of existingChild.
     *
     * @param newChild
     * @param existingChild
     */
    public void addAt( Strategy newChild, Strategy existingChild )
    {
        int i = super.getIndex( existingChild );
        if( i != -1 )
            ((Strategy) super.getChildAt( i )).add( newChild );
    }

    /**
     * Remove the existing child (first occurrence) from the strategy node.
     *
     * @param existingChild
     */
    public void remove( Strategy existingChild )
    {
        super.remove( existingChild );
    }

    ////////////
    // OBJECT //
    ////////////
    /**
     * Give a string representation of the strategy node. Notation is following a program flow chart: diamonds represent conditions, rectangles define
     * activities.
     *
     * @return
     */
    public String toString()
    {
        if( this.isCondition )
            return "< " + this.userObject.toString() + " >";
        return "[ " + this.userObject.toString() + " ]";
    }

    /**
     * Checks whether this node equals the given one in type and name.
     *
     * @param o
     * @return true if this node equals the given one in type and name, false otherwise
     */
    public boolean equals( Object o )
    {
        if( o instanceof DefaultMutableTreeNode )
        {
            DefaultMutableTreeNode n = (DefaultMutableTreeNode) o;
            return super.equals( n );
        }
        if( !(o instanceof Strategy) )
            return false;
        Strategy s = (Strategy) o;
        return this.isCondition == s.isCondition() && this.userObject.equals( s );
    }
}
