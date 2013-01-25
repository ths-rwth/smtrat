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
import edu.uci.ics.jung.visualization.VisualizationServer;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.AbstractGraphMousePlugin;
import edu.uci.ics.jung.visualization.picking.PickedState;
import java.awt.Color;
import java.awt.Cursor;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.event.InputEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.geom.Point2D;
import java.awt.geom.Rectangle2D;
import java.util.Collection;

/**
 * @file PickingGraphMousePlugin.java
 *
 * @author  Henrik Schmitz
 * @since   2012-09-26
 * @version 2012-11-19
 */
public class PickingGraphMousePlugin extends AbstractGraphMousePlugin implements MouseListener, MouseMotionListener
{   
    private final VisualizationServer.Paintable lensPaintable;
    private final Rectangle2D rectangle = new Rectangle2D.Float();
    private final VisualizationViewer visualization;
    
    private Point mouseDown;
    private Vertex pickedVertex;

    public PickingGraphMousePlugin( GUI gui )
    {
        super( InputEvent.BUTTON1_MASK );
        lensPaintable = new LensPaintable();
        visualization = gui.getVisualization();
    }

    @Override
    public void mouseClicked( MouseEvent me ){}
    
    @Override
    public void mouseDragged( MouseEvent me )
    {
        if( pickedVertex!=null )
        {
            Point p = me.getPoint();
            Point2D graphPoint = visualization.getRenderContext().getMultiLayerTransformer().inverseTransform( p );
            Point2D graphDown = visualization.getRenderContext().getMultiLayerTransformer().inverseTransform( mouseDown );
            Layout<Vertex,Edge> layout = visualization.getGraphLayout();
            double dx = graphPoint.getX()-graphDown.getX();
            double dy = graphPoint.getY()-graphDown.getY();
            PickedState<Vertex> pickedVertexState = visualization.getPickedVertexState();
            for( Vertex v : pickedVertexState.getPicked() )
            {
                if( v!=null )
                {
                    Point2D vp = layout.transform( v );
                    vp.setLocation( vp.getX()+dx, vp.getY()+dy );
                    layout.setLocation( v, vp );
                }
            }
            mouseDown = p;
        }
        else
        {
            Point mouseOut = me.getPoint();
            if( me.getModifiers()==modifiers )
            {
                rectangle.setFrameFromDiagonal( mouseDown, mouseOut );
            }
            visualization.repaint();
        }
    }

    @Override
    public void mouseEntered( MouseEvent me ){}

    @Override
    public void mouseExited( MouseEvent me ){}

    @Override
    public void mouseMoved( MouseEvent me )
    {
        Point p = me.getPoint();
        GraphElementAccessor<Vertex,Edge> pickSupport = visualization.getPickSupport();
        if( pickSupport!=null )
        {
            pickedVertex = pickSupport.getVertex( visualization.getModel().getGraphLayout(), p.getX(), p.getY() );
            if( pickedVertex!=null )
            {
                visualization.setCursor( Cursor.getPredefinedCursor( Cursor.HAND_CURSOR ) );
            }
            else
            {
                visualization.setCursor( Cursor.getPredefinedCursor( Cursor.DEFAULT_CURSOR ) );
            }
        }
    }
    
    @Override
    public void mousePressed( MouseEvent me )
    {
        mouseDown = me.getPoint();
        GraphElementAccessor<Vertex,Edge> pickSupport = visualization.getPickSupport();
        PickedState<Vertex> pickedVertexState = visualization.getPickedVertexState();
        if( me.getModifiers()==modifiers )
        {
            if( pickSupport!=null && pickedVertexState!=null )
            {
                Layout<Vertex,Edge> layout = visualization.getGraphLayout();
                rectangle.setFrameFromDiagonal( mouseDown, mouseDown );
                Point2D ip = mouseDown;
                pickedVertex = pickSupport.getVertex( layout, ip.getX(), ip.getY() );
                if( pickedVertex!=null )
                {
                    if( !pickedVertexState.isPicked( pickedVertex ) )
                    {
                        pickedVertexState.clear();
                        pickedVertexState.pick( pickedVertex, true );
                    }
                }
                else
                {
                    visualization.addPostRenderPaintable( lensPaintable );
                    pickedVertexState.clear();
                }
            }
        }
        else
        {
            pickedVertexState.clear();
        }
    }

    @Override
    public void mouseReleased( MouseEvent me )
    {
        PickedState<Vertex> pickedVertexState = visualization.getPickedVertexState();
        if( me.getModifiers()==modifiers )
        {
            if( mouseDown!=null )
            {
                Point mouseOut = me.getPoint();
                if( pickedVertex==null && notTooClose( mouseDown, mouseOut, 5.0d ) )
                {
                    pickContainedVertices( visualization, mouseDown, mouseOut, true );
                }
                if( pickedVertexState.isPicked( pickedVertex ) )
                {
                    pickedVertexState.clear();
                }
            }
        }
        mouseDown = null;
        pickedVertex = null;
        rectangle.setFrame( 0.0d, 0.0d, 0.0d, 0.0d );
        visualization.removePostRenderPaintable( lensPaintable );
        visualization.repaint();
    }
    
    private boolean notTooClose( Point2D p, Point2D q, double min )
    {
       return !( Math.abs( p.getX()-q.getX() )<min && Math.abs( p.getY()-q.getY() )<min );
    }
    
    /**
     * pick the vertices inside the rectangle created from points
     * 'down' and 'out'
     *
     */
    private void pickContainedVertices( VisualizationViewer<Vertex,Edge> visualization, Point2D mouseDown, Point2D mouseOut, boolean clear )
    {    
        Layout<Vertex,Edge> layout = visualization.getGraphLayout();
        PickedState<Vertex> pickedVertexState = visualization.getPickedVertexState();
        Rectangle2D pickRectangle = new Rectangle2D.Double();
        pickRectangle.setFrameFromDiagonal( mouseDown, mouseOut );
        if( pickedVertexState!=null )
        {
            if( clear )
            {
            	pickedVertexState.clear();
            }
            GraphElementAccessor<Vertex,Edge> pickSupport = visualization.getPickSupport();
            Collection<Vertex> picked = pickSupport.getVertices( layout, pickRectangle );
            for( Vertex v : picked )
            {
            	pickedVertexState.pick( v, true );
            }
        }
    }
    
    /**
     * a Paintable to draw the rectangle used to pick multiple
     * Vertices
     * @author Tom Nelson
     *
     */
    private class LensPaintable implements VisualizationServer.Paintable
    {      
        @Override
        public void paint( Graphics g )
        {
            g.setColor( Color.CYAN );
            ((Graphics2D) g).draw( rectangle );
        }

        @Override
        public boolean useTransform()
        {
            return false;
        }
    }
}