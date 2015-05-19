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