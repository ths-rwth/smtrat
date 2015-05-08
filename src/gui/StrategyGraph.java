import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.graph.util.EdgeType;
import edu.uci.ics.jung.graph.util.Pair;
import java.awt.geom.Point2D;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

/**
 * @file StrategyGraph.java
 *
 * @author  Henrik Schmitz
 * @since   2012-09-22
 * @version 2012-11-19
 */
public class StrategyGraph extends DirectedSparseGraph
{   
    public static final String ROOT_VERTEX_MODULE_NAME = "Start";

    private final Vertex rootVertex;
    
    public static int priorityAllocator;

    public StrategyGraph()
    {
        super();
        priorityAllocator = 0;
        rootVertex = new Vertex( new Module( ROOT_VERTEX_MODULE_NAME, "MT_" + ROOT_VERTEX_MODULE_NAME ) );
        addVertex( rootVertex );
    }
    
    public boolean addEdge( Edge edge, Vertex fromVertex, Vertex toVertex )
    {
        boolean ret = super.addEdge( edge, fromVertex, toVertex );
        if( ret )
        {
            priorityAllocator++;
        }
        return ret;
    }
    
    public boolean addEdge( Edge edge, Vertex fromVertex, Vertex toVertex, EdgeType type ) throws UnsupportedStrategyGraphOperationException
    {
        if( hasPath( toVertex, fromVertex ) )
        {
            boolean ret = super.addEdge( edge, fromVertex, toVertex, type );
            if( ret )
            {
                priorityAllocator++;
            }
            return ret;
        }
        else
        {
            throw new UnsupportedStrategyGraphOperationException( UnsupportedStrategyGraphOperationException.TWO_SUCCESSOR_VERTICES_CANNOT_MERGE_AGAIN );
        }
    }
    
    public Edge getEdge( Point2D point )
    {
        for( Edge e : (Collection<Edge>) this.getEdges() )
        {
            if( e!=null && e.getLabelBounds().contains( point ) )
            {
                return e;
            }
        }
        return null;
    }
    
    public Vertex getRoot()
    {
        return rootVertex;
    }
    
    public Edge getPredecesssorEdge( Edge edge )
    {
        return getPredecesssorEdge( (Vertex) this.getEndpoints( edge ).getFirst() );
    }
    
    public Edge getPredecesssorEdge( Vertex vertex )
    {
        for( Edge e : (Collection<Edge>) this.getInEdges( vertex ) )
        {
            if( !e.isBackLink() )
            {
                return e;
            }
        }
        return null;
    }
    
    public void pushPriority( Edge edge1, Edge edge2 ) throws UnsupportedStrategyGraphOperationException
    {
        if( edge1!=null && edge2!=null && edge1!=edge2 )
        {
            Pair<Vertex> vertexPair1 = this.getEndpoints( edge1 );
            Pair<Vertex> vertexPair2 = this.getEndpoints( edge2 );
            if( ( edge1.isBackLink() || !hasPath( vertexPair1.getSecond(), vertexPair2.getFirst() ) ) && ( edge2.isBackLink() || !hasPath( vertexPair2.getSecond(), vertexPair1.getFirst() ) ) )
            {
                if( edge1.getPriority()<edge2.getPriority() )
                {
                    throw new StrategyGraph.UnsupportedStrategyGraphOperationException( StrategyGraph.UnsupportedStrategyGraphOperationException.STARTING_EDGE_MUST_HAVE_LOWER_PRIORITY );
                }
                Edge highPriorityEdge, lowPriorityEdge;
                if( edge1.getPriority()>edge2.getPriority() )
                {
                    highPriorityEdge = edge2;
                    lowPriorityEdge = edge1;
                }
                else
                {
                    highPriorityEdge = edge1;
                    lowPriorityEdge = edge2;
                }
                int lowerBound = highPriorityEdge.getPriority();
                int upperBound = lowPriorityEdge.getPriority();
                
                ArrayList<Edge> higherPriorityEdges = new ArrayList<>();
                collectHigherPriorityEdges( higherPriorityEdges, lowPriorityEdge, lowerBound, upperBound );
                Collections.sort( higherPriorityEdges );
                
                ArrayList<Edge> lowerPriorityEdges = new ArrayList<>();
                for( Edge e : (Collection<Edge>) this.getEdges() )
                {
                    if( !higherPriorityEdges.contains( e ) && e.getPriority()>=lowerBound && e.getPriority()<upperBound )
                    {
                        lowerPriorityEdges.add( e );
                    }
                }
                Collections.sort( lowerPriorityEdges );
                
                int currentPriority = lowerBound;
                for( int i=0; i<higherPriorityEdges.size(); i++ )
                {
                    higherPriorityEdges.get( i ).setPriority( currentPriority++ );
                }
                for( int i=0; i<lowerPriorityEdges.size(); i++ )
                {
                    lowerPriorityEdges.get( i ).setPriority( currentPriority++ );
                }
            }
            else
            {
                throw new UnsupportedStrategyGraphOperationException( UnsupportedStrategyGraphOperationException.EDGES_ON_SAME_PATH_CANNOT_CHANGE_PRIORITIES );
            }
        }
    }
    
    public void removeEdge( Edge edge )
    {
        if ( !containsEdge( edge ) )
        {
            return;
        }
        Vertex successorVertex = (Vertex) this.getEndpoints( edge ).getSecond();
        super.removeEdge( edge );
        if( successorVertex!=null && !hasPath( rootVertex, successorVertex ) )
        {
            removeNotConnectedVertices( successorVertex );
        }
        clearUpPriorities();
    }
    
    public void removeVertex( Vertex vertex )
    {
        removeNotConnectedVertices( vertex );
        clearUpPriorities();
    }
    
    private void clearUpPriorities()
    {
        ArrayList<Edge> edgeList = new ArrayList<>( (Collection<Edge>) this.getEdges() );
        Collections.sort( edgeList );
        int i = 0;
        for( ; i<edgeList.size(); i++ )
        {
            edgeList.get( i ).setPriority( i );
        }
        priorityAllocator = i;
    }

    private void collectHigherPriorityEdges( ArrayList<Edge> edgeList, Edge edge, int lowerBound, int upperBound )
    {
        edgeList.add( edge );
        Edge predecessorEdge = this.getPredecesssorEdge( edge );
        if( predecessorEdge!=null && predecessorEdge.getPriority()>lowerBound && predecessorEdge.getPriority()<upperBound )
        {
            collectHigherPriorityEdges( edgeList, predecessorEdge, lowerBound, upperBound );
        }
    }

    private boolean hasPath( Vertex fromVertex, Vertex toVertex )
    {
        if( fromVertex==toVertex )
        {
            return true;
        }
        Collection<Edge> outEdges = this.getOutEdges( fromVertex );
        for( Edge e : outEdges )
        {
            if ( e!=null && !e.isBackLink() )
            {
                if( hasPath( (Vertex) this.getEndpoints( e ).getSecond(), toVertex ) )
                {
                    return true;
                }
            }
        }
        return false;
    }
    
    private void removeNotConnectedVertices( Vertex vertex )
    {
        if ( !containsVertex( vertex ) )
        {
            return;
        }
        Collection<Vertex> neighborVertices = this.getNeighbors( vertex );
        super.removeVertex( vertex );
        for( Vertex v : neighborVertices )
        {
            if( v!=null && !hasPath( rootVertex, v ) )
            {
                removeNotConnectedVertices( v );
            }
        }
    }
    
    public static class UnsupportedStrategyGraphOperationException extends Exception
    {
        public static final String EDGES_CANNOT_POINT_TO_START_VERTEX = "Edges cannot point to start vertex.";
        public static final String EDGES_ON_SAME_PATH_CANNOT_CHANGE_PRIORITIES = "Edges on the same path cannot change priorities with each other.";
        public static final String PARALLEL_EDGES_ARE_NOT_ALLOWED = "Parallel edges are not allowed.";
        public static final String STARTING_EDGE_MUST_HAVE_LOWER_PRIORITY = "Source edge must have lower priority than destination edge.";
        public static final String TWO_SUCCESSOR_VERTICES_CANNOT_MERGE_AGAIN = "Two successor vertices cannot merge again.";
        private static final String INSTRUCTION_HINT = " Please read the instructions for further details.";

        public UnsupportedStrategyGraphOperationException( String s )
        {
            super( s + INSTRUCTION_HINT );
        }
    }
}