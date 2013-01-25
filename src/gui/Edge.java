/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2013 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT. If not, see <http://www.gnu.org/licenses/>.
 *
 */

import java.awt.Rectangle;

/**
 * @file Edge.java
 *
 * @author  Henrik Schmitz
 * @since   2012-09-24
 * @version 2012-11-13
 */
public class Edge implements Comparable<Edge>
{
    final private boolean backLink;
    private Condition condition;
    private int priority;
    private Rectangle labelBounds;

    public Edge( Condition condition )
    {
        this( condition, false );
    }

    public Edge( Condition condition, boolean backLink )
    {
        this( condition, backLink, StrategyGraph.priorityAllocator );
    }
    
    public Edge( Condition condition, boolean backLink, int priority )
    {
        this.condition = condition;
        this.priority = priority;
        this.backLink = backLink;
        labelBounds = new Rectangle();
    }
    
    @Override
    public int compareTo( Edge e )
    {
        if( this.getPriority()<e.getPriority() )
        {
            return -1;
        }
        else if( this.getPriority()==e.getPriority() )
        {
            return 0;
        }
        else
        {
            return 1;
        }
    }
    
    public Condition getCondition()
    {
        return condition;
    }
    
    public Rectangle getLabelBounds()
    {
        return labelBounds;
    }
    
    public int getPriority()
    {
        return priority;
    }
    
    public boolean isBackLink()
    {
        return backLink;
    }
    
    public void setCondition( Condition condition )
    {
        this.condition = condition;
    }
    
    public void setLabelBounds( Rectangle bounds )
    {
        this.labelBounds = bounds;
    }
    
    public void setPriority( int priority )
    {
        this.priority = priority;
    }

    @Override
    public String toString()
    {
        return "(" + getPriority() + ")";
    }
}