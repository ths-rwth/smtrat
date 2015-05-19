/*
 * Copyright (c) 2005, the JUNG Project and the Regents of the University of
 * California
 * All rights reserved.
 *
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 *
 */

import edu.uci.ics.jung.algorithms.layout.GraphElementAccessor;
import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.graph.util.EdgeType;
import edu.uci.ics.jung.visualization.VisualizationServer;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.AbstractGraphMousePlugin;
import edu.uci.ics.jung.visualization.util.ArrowFactory;
import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Cursor;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.Shape;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.geom.AffineTransform;
import java.awt.geom.Point2D;
import java.awt.geom.QuadCurve2D;
import javax.swing.AbstractAction;
import javax.swing.JOptionPane;
import javax.swing.JPopupMenu;

/**
 * @file EditingGraphMousePlugin.java
 *
 * @author  Henrik Schmitz
 * @since   2012-09-26
 * @version 2012-11-19
 */
public class EditingGraphMousePlugin extends AbstractGraphMousePlugin implements MouseListener, MouseMotionListener
{
    private final Shape rawArrowShape;
    private final QuadCurve2D.Double rawEdgeShape;
    private final VisualizationServer.Paintable arrowPaintable;
    private final VisualizationServer.Paintable edgePaintable;
    private final GUI gui;
    private final VisualizationViewer visualization;
    private final JPopupMenu popupMenuVertex, popupMenuRootVertex, popupMenuEdgeLabel;
    
    private enum popupType { EdgeLabel, RootVertex, Vertex };
    
    private Point2D mouseDown;
    private Edge pickedEdge, startEdge;
    private Vertex pickedVertex, startVertex;
    private StrategyGraph graph;
    private Shape arrowShape, edgeShape;

    /**
     * create instance and prepare shapes for visual effects
     * @param modifiers
     */
    public EditingGraphMousePlugin( GUI gui )
    {
        super( InputEvent.BUTTON3_MASK );
        rawArrowShape = ArrowFactory.getNotchedArrow( 12.0f, 16.0f, 8.0f );
        rawEdgeShape = new QuadCurve2D.Double( 0.0d, 0.0d, 0.0d, 0.0d, 1.0d, 0.0d );
        arrowPaintable = new EditingGraphMousePlugin.ArrowPaintable();
        edgePaintable = new EditingGraphMousePlugin.EdgePaintable();
        popupMenuVertex = setupPopupMenu( popupType.Vertex );
        popupMenuRootVertex = setupPopupMenu( popupType.RootVertex );
        popupMenuEdgeLabel = setupPopupMenu( popupType.EdgeLabel );
        this.gui = gui;
        visualization = gui.getVisualization();
    }

    @Override
    public void mouseClicked( MouseEvent me )
    {
        if( checkModifiers( me ) )
        {
            Point p = me.getPoint();
            graph = (StrategyGraph) visualization.getGraphLayout().getGraph();
            if( (pickedEdge = graph.getEdge( p ))!=null )
            {
                popupMenuEdgeLabel.show( visualization, p.x, p.y );
            }
            else
            {
                GraphElementAccessor<Vertex,Edge> pickSupport = visualization.getPickSupport();
                if( pickSupport!=null )
                {
                    pickedVertex = pickSupport.getVertex( visualization.getModel().getGraphLayout(), p.getX(), p.getY() );
                    if( pickedVertex!=null )
                    {
                        if( pickedVertex==graph.getRoot() )
                        {
                            popupMenuRootVertex.show( visualization, p.x, p.y );
                        }
                        else
                        {
                            popupMenuVertex.show( visualization, p.x, p.y );
                        }
                    }
                }
            }
        }
    }

    /**
     * If startVertex is non-null, stretch an edge shape between
     * startVertex and the mouse pointer to simulate edge creation
     */
    @Override
    public void mouseDragged( MouseEvent me )
    {
        if( checkModifiers( me ) )
        {
            if( startVertex!=null || startEdge!=null )
            {
                Point p = me.getPoint();
                transformEdgeShape( mouseDown, p );
                transformArrowShape( mouseDown, p );
                visualization.setCursor( Cursor.getPredefinedCursor( Cursor.CROSSHAIR_CURSOR ) );
            }
            visualization.repaint();
        }
    }

    @Override
    public void mouseEntered( MouseEvent me ){}

    @Override
    public void mouseExited( MouseEvent me ){}

    @Override
    public void mouseMoved( MouseEvent me ){}
    
    /**
     * If the mouse is pressed in an empty area, create a new vertex there.
     * If the mouse is pressed on an existing vertex, prepare to create
     * an edge from that vertex to another
     */
    @Override
	public void mousePressed( MouseEvent me )
    {
        if( checkModifiers( me ) )
        {
            boolean overElement = false;
            Point p = me.getPoint();
            graph = (StrategyGraph) visualization.getGraphLayout().getGraph();
            if( (startEdge = graph.getEdge( p ))!=null )
            {
                overElement = true;
            }
            else
            {
                GraphElementAccessor<Vertex,Edge> pickSupport = visualization.getPickSupport();
                if( pickSupport!=null )
                {
                    pickedVertex = pickSupport.getVertex( visualization.getModel().getGraphLayout(), p.getX(), p.getY() );
                    if( (startVertex = pickedVertex)!=null )
                    {
                        overElement = true;
                    }
                }
            }
            if( overElement )
            {
                mouseDown = p;
                transformEdgeShape( mouseDown, mouseDown );
                visualization.addPostRenderPaintable( edgePaintable );
                transformArrowShape( mouseDown, mouseDown );
                visualization.addPostRenderPaintable( arrowPaintable );
            }
        }
    }
    
    /**
     * If startVertex is non-null, and the mouse is released over an
     * existing vertex, create an undirected edge from startVertex to
     * the vertex under the mouse pointer. If shift was also pressed,
     * create a directed edge instead.
     */
    @Override
	public void mouseReleased( MouseEvent me )
    {
        if( checkModifiers( me ) )
        {
            Point p = me.getPoint();
            try
            {
                graph = (StrategyGraph) visualization.getGraphLayout().getGraph();
                if( startEdge!=null )
                {
                    if( (pickedEdge = graph.getEdge( p ))!=null && startEdge!=pickedEdge )
                    {
                        graph.pushPriority( startEdge, pickedEdge );
                        visualization.fireStateChanged();
                        visualization.repaint();
                    }
                }
                else
                {
                    Layout<Vertex,Edge> layout = visualization.getModel().getGraphLayout();
                    GraphElementAccessor<Vertex,Edge> pickSupport = visualization.getPickSupport();
                    if( pickSupport!=null )
                    {
                        pickedVertex = pickSupport.getVertex( layout, p.getX(), p.getY() );
                        if( pickedVertex!=null && startVertex!=null && pickedVertex!=startVertex && pickedVertex!=graph.getRoot() )
                        {
                            if( !graph.getSuccessors( startVertex ).contains( pickedVertex ) )
                            {
                                pickedEdge = new Edge( new Condition(), true );
                                if( graph.addEdge( pickedEdge, startVertex, pickedVertex, EdgeType.DIRECTED ) )
                                {
                                    EditStrategyGraphDialog.showAddEdgeDialog( gui, pickedEdge );
                                }
                            }
                            else
                            {
                                throw new StrategyGraph.UnsupportedStrategyGraphOperationException( StrategyGraph.UnsupportedStrategyGraphOperationException.PARALLEL_EDGES_ARE_NOT_ALLOWED );
                            }
                        }
                        else if( pickedVertex!=null && pickedVertex!=startVertex && pickedVertex==graph.getRoot() )
                        {
                            throw new StrategyGraph.UnsupportedStrategyGraphOperationException( StrategyGraph.UnsupportedStrategyGraphOperationException.EDGES_CANNOT_POINT_TO_START_VERTEX );
                        }
                    }
                }
            }
            catch( StrategyGraph.UnsupportedStrategyGraphOperationException ex )
            {
                JOptionPane.showMessageDialog( gui, ex.getMessage(), "Information", JOptionPane.INFORMATION_MESSAGE );
            }
            visualization.setCursor( Cursor.getPredefinedCursor( Cursor.DEFAULT_CURSOR ) );
            startEdge = null;
            startVertex = null;
            mouseDown = null;
            visualization.removePostRenderPaintable( edgePaintable );
            visualization.removePostRenderPaintable( arrowPaintable );
            visualization.repaint();
        }
    }
    
    private JPopupMenu setupPopupMenu( popupType type )
    {
        JPopupMenu popupMenu = new JPopupMenu();
        switch( type )
        {
            case EdgeLabel:
                popupMenu.add( new AbstractAction( EditStrategyGraphDialog.EDIT_EDGE )
                {
                    @Override
                    public void actionPerformed( ActionEvent e )
                    {
                        EditStrategyGraphDialog.showEditEdgeDialog( gui, pickedEdge );
                    }
                });
                popupMenu.add( new AbstractAction( EditStrategyGraphDialog.DELETE_EDGE )
                {
                    @Override
                    public void actionPerformed( ActionEvent e )
                    {
                        graph.removeEdge( pickedEdge );
                        visualization.fireStateChanged();
                        visualization.repaint();
                    } 
                });
                break;
            case RootVertex:
                popupMenu.add( new AbstractAction( EditStrategyGraphDialog.ADD_VERTEX_AND_EDGE )
                {
                    @Override
                    public void actionPerformed( ActionEvent e )
                    {
                        EditStrategyGraphDialog.showAddVertexAndEdgeDialog( gui, pickedVertex );
                    }
                });
                break;
            case Vertex:
                popupMenu.add( new AbstractAction( EditStrategyGraphDialog.ADD_VERTEX_AND_EDGE )
                {
                    @Override
                    public void actionPerformed( ActionEvent e )
                    {
                        EditStrategyGraphDialog.showAddVertexAndEdgeDialog( gui, pickedVertex );
                    }
                });
                popupMenu.add( new AbstractAction( EditStrategyGraphDialog.EDIT_VERTEX )
                {
                    @Override
                    public void actionPerformed( ActionEvent e )
                    {
                        EditStrategyGraphDialog.showEditVertexDialog( gui, pickedVertex );
                    }
                });
                popupMenu.add( new AbstractAction( EditStrategyGraphDialog.DELETE_VERTEX )
                {
                    @Override
                    public void actionPerformed( ActionEvent e )
                    {
                        graph.removeVertex( pickedVertex );
                        visualization.fireStateChanged();
                        visualization.repaint();
                    }
                });
                break;
        }
        return popupMenu;
    }
    
    private void transformArrowShape( Point2D mouseDown, Point2D mouseOut )
    {
        float x1 = (float) mouseDown.getX();
        float y1 = (float) mouseDown.getY();
        float x2 = (float) mouseOut.getX();
        float y2 = (float) mouseOut.getY();

        AffineTransform xform = AffineTransform.getTranslateInstance( x2, y2 );
        
        float dx = x2-x1;
        float dy = y2-y1;
        float thetaRadians = (float) Math.atan2( dy, dx );
        xform.rotate( thetaRadians );
        arrowShape = xform.createTransformedShape( rawArrowShape );
    }
    
    /**
     * code lifted from PluggableRenderer to move an edge shape into an
     * arbitrary position
     */
    private void transformEdgeShape( Point2D mouseDown, Point2D mouseOut )
    {
        float x1 = (float) mouseDown.getX();
        float y1 = (float) mouseDown.getY();
        float x2 = (float) mouseOut.getX();
        float y2 = (float) mouseOut.getY();

        AffineTransform xform = AffineTransform.getTranslateInstance( x1, y1 );
        
        float dx = x2-x1;
        float dy = y2-y1;
        float thetaRadians = (float) Math.atan2( dy, dx );
        xform.rotate( thetaRadians );
        float dist = (float) Math.sqrt( dx*dx+dy*dy );
        xform.scale( dist/rawEdgeShape.getBounds().getWidth(), 1.0 );
        edgeShape = xform.createTransformedShape( rawEdgeShape );
    }
    
    /**
     * Used for the directed edge creation visual effect during mouse drag
     */
    private class ArrowPaintable implements VisualizationServer.Paintable
    {    
        @Override
        public void paint( Graphics g )
        {
            if( arrowShape!=null )
            {
                if( startEdge!=null )
                {
                    g.setColor( Color.GRAY );
                }
                else
                {
                    g.setColor( Color.BLACK );
                }
                ((Graphics2D) g).fill( arrowShape );
            }
        }
        
        @Override
        public boolean useTransform()
        {
            return false;
        }
    }

    /**
     * Used for the edge creation visual effect during mouse drag
     */
    private class EdgePaintable implements VisualizationServer.Paintable
    {    
        private final BasicStroke dashedStroke =  new BasicStroke( 2f, BasicStroke.CAP_BUTT, BasicStroke.JOIN_MITER, 10.0f, new float[] { 7.5f}, 0.0f );
        
        @Override
        public void paint( Graphics g )
        {
            if( edgeShape!=null )
            {
                if( startEdge!=null )
                {
                    g.setColor( Color.PINK );
                    ((Graphics2D) g).setStroke( dashedStroke );
                }
                else
                {
                    g.setColor( GUI.EDGE_COLOR );
                }
                ((Graphics2D) g).draw( edgeShape );
            }
        }
        
        @Override
        public boolean useTransform()
        {
            return false;
        }
    }
}