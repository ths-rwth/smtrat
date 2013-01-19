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

import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.Context;
import edu.uci.ics.jung.graph.util.Pair;
import edu.uci.ics.jung.visualization.Layer;
import edu.uci.ics.jung.visualization.RenderContext;
import edu.uci.ics.jung.visualization.renderers.Renderer;
import edu.uci.ics.jung.visualization.transform.shape.GraphicsDecorator;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Rectangle;
import java.awt.Shape;
import java.awt.geom.AffineTransform;
import java.awt.geom.Point2D;
import java.awt.geom.QuadCurve2D;
import java.io.File;
import javax.swing.ImageIcon;

/**
 * @file EdgeLabelRendering.java
 *       - needs file "smtrat/htdocs/images/rectangle_green.png"
 *       - needs file "smtrat/htdocs/images/rectangle_orange.png"
 *
 * @author  Henrik Schmitz
 * @since   2012-09-21
 * @version 2012-11-20
 */
public class EdgeLabelRendering implements Renderer.EdgeLabel<Vertex,Edge>
{
    // Green of rectangle is #00bb00
    private static final ImageIcon SQUARE_GREEN = new ImageIcon( IOTools.SMTRAT_GRAPHICS_DIR + File.separator + "rectangle_green.png" );
    // Orange of rectangle is #ffa000
    private static final ImageIcon SQUARE_ORANGE = new ImageIcon( IOTools.SMTRAT_GRAPHICS_DIR + File.separator + "rectangle_orange.png" );
    
    private static final int SQUARE_EDGE_LENGTH = 10;
    
    @Override
    public void labelEdge( RenderContext<Vertex,Edge> renderContext, Layout<Vertex,Edge> layout, Edge edge, String label )
    {
    	if( label==null || label.length()==0 )
        {
            return;
        }

        // don't draw edge if either incident vertex is not drawn
        StrategyGraph graph = (StrategyGraph) layout.getGraph();
        Pair<Vertex> endpoints = graph.getEndpoints( edge );
        Vertex v1 = endpoints.getFirst();
        Vertex v2 = endpoints.getSecond();
        if ( !renderContext.getEdgeIncludePredicate().evaluate( Context.<Graph<Vertex,Edge>,Edge>getInstance( graph, edge ) ) )
        {
            return;
        }
        if ( !renderContext.getVertexIncludePredicate().evaluate( Context.<Graph<Vertex,Edge>,Vertex>getInstance( graph, v1 ) ) || !renderContext.getVertexIncludePredicate().evaluate( Context.<Graph<Vertex,Edge>,Vertex>getInstance( graph, v2 ) ) )
        {
            return;
        }

        Point2D p1 = layout.transform( v1 );
        Point2D p2 = layout.transform( v2 );
        p1 = renderContext.getMultiLayerTransformer().transform( Layer.LAYOUT, p1 );
        p2 = renderContext.getMultiLayerTransformer().transform( Layer.LAYOUT, p2 );
        float x1 = (float) p1.getX();
        float y1 = (float) p1.getY();
        float x2 = (float) p2.getX();
        float y2 = (float) p2.getY();

        GraphicsDecorator graphicsDecorator = renderContext.getGraphicsContext();
        float distX = x2-x1;
        float distY = y2-y1;
        double totalLength = Math.sqrt( distX*distX+distY*distY );

        double closeness = renderContext.getEdgeLabelClosenessTransformer().transform( Context.<Graph<Vertex,Edge>,Edge>getInstance( graph, edge ) ).doubleValue();

        int posX = (int) ( x1+closeness*distX );
        int posY = (int) ( y1+closeness*distY );

        Shape edgeShape = renderContext.getEdgeShapeTransformer().transform( Context.<Graph<Vertex,Edge>,Edge>getInstance( graph, edge ) );

        int labelOffset = (int) ((QuadCurve2D) edgeShape).getCtrlY();
        if( labelOffset==0 )
        {
            labelOffset = 5;
        }
        else
        {
            labelOffset = -labelOffset/2;
        }
        int xDisplacement = (int) ( labelOffset*(distY/totalLength) );
        int yDisplacement = (int) ( labelOffset*(-distX/totalLength) );

        Component component = prepareRenderer( renderContext, label, renderContext.getPickedEdgeState().isPicked( edge ), edge );
        
        Dimension dimension = component.getPreferredSize();
        
        double parallelOffset = 1;
        parallelOffset += renderContext.getParallelEdgeIndexFunction().getIndex( graph, edge );
        parallelOffset *= dimension.height;
        
        AffineTransform oldTransform = graphicsDecorator.getTransform();
        AffineTransform xTransform = new AffineTransform( oldTransform );
        xTransform.translate( posX+xDisplacement, posY+yDisplacement );
        double dx = x2-x1;
        double dy = y2-y1;
        // If label is parallel to edge
        if( renderContext.getEdgeLabelRenderer().isRotateEdgeLabels() )
        {
            double theta = Math.atan2( dy, dx );
            if( dx<0 ) {
                theta += Math.PI;
            }
            xTransform.rotate( theta );
        }
        if( dx<0 ) {
            parallelOffset = -parallelOffset;
        }
        
        xTransform.translate( -dimension.width/2, -(dimension.height/2-parallelOffset) );
        graphicsDecorator.setTransform( xTransform );

        int maxHeight = Math.max( SQUARE_EDGE_LENGTH, dimension.height );
        int padding = 3;
        int enlargeBoundsWidth = 4;
        graphicsDecorator.draw( component, renderContext.getRendererPane(), 0, (maxHeight-dimension.height)/2, dimension.width, dimension.height, true );
        if( edge.getCondition().isTrueCondition() )
        {
            graphicsDecorator.draw( SQUARE_GREEN, null, null, dimension.width+padding+SQUARE_EDGE_LENGTH/2, (maxHeight-SQUARE_EDGE_LENGTH)/2+SQUARE_EDGE_LENGTH/2 );
        }
        else
        {
            graphicsDecorator.draw( SQUARE_ORANGE, null, null, dimension.width+padding+SQUARE_EDGE_LENGTH/2, (maxHeight-SQUARE_EDGE_LENGTH)/2+SQUARE_EDGE_LENGTH/2 );
        }
        
        Rectangle bounds = new Rectangle( (int) xTransform.getTranslateX(), (int) xTransform.getTranslateY(), dimension.width+padding+SQUARE_EDGE_LENGTH+enlargeBoundsWidth, maxHeight );
        edge.setLabelBounds( bounds );

        graphicsDecorator.setTransform( oldTransform );
    }

    private Component prepareRenderer( RenderContext<Vertex,Edge> renderContext, Object value, boolean isSelected, Edge edge )
    {
		return renderContext.getEdgeLabelRenderer().<Edge>getEdgeLabelRendererComponent( renderContext.getScreenDevice(), value, renderContext.getEdgeFontTransformer().transform( edge ), isSelected, edge );
	}
}