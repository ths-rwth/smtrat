import edu.uci.ics.jung.algorithms.layout.FRLayout;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.Context;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.PluggableGraphMouse;
import edu.uci.ics.jung.visualization.decorators.ConstantDirectionalEdgeValueTransformer;
import edu.uci.ics.jung.visualization.decorators.ToStringLabeller;
import edu.uci.ics.jung.visualization.picking.PickedState;
import edu.uci.ics.jung.visualization.renderers.DefaultEdgeLabelRenderer;
import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Point;
import java.awt.Shape;
import java.awt.Stroke;
import java.awt.Toolkit;
import java.awt.Desktop;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.awt.event.MouseEvent;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import java.awt.geom.QuadCurve2D;
import java.io.File;
import javax.swing.AbstractAction;
import javax.swing.ImageIcon;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.KeyStroke;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import org.apache.commons.collections15.Transformer;
import org.apache.commons.collections15.functors.ConstantTransformer;

/**
 * @file GUI.java
 *       - needs file "smtrat/htdocs/images/icon.png"
 *       - needs file "smtrat/htdocs/images/logoBig.png"
 *
 * @author  Henrik Schmitz
 * @since   2012-09-21
 * @version 2012-11-20
 */
public class GUI extends JFrame implements WindowListener
{
    // GUI
    public static final String TITLE = "SMT-XRAT";
// HTML_ABOUT to be changed
    public static final String HTML_ABOUT = "<html><p>" + TITLE + " is a graphical user interface to<br />export and manage SMT Solvers according<br />to a user-defined strategy.<br /><br />Support:<br />Florian Corzilius (<a href=\"mailto:corzilius@cs.rwth-aachen.de\">corzilius@cs.rwth-aachen.de</a>)<br />Gereon Kremer (<a href=\"mailto:gereon.kremer@cs.rwth-aachen.de\">gereon.kremer@cs.rwth-aachen.de</a>)<br />Sebastian Junges (<a href=\"mailto:sebastian.junges@cs.rwth-aachen.de\">sebastian.junges@cs.rwth-aachen.de</a>)<br />Stefan Schupp (<a href=\"mailto:stefan.schupp@cs.rwth-aachen.de\">stefan.schupp@cs.rwth-aachen.de</a>)<br /><br />GUI by Henrik Schmitz.<br /><br />Copyright (C) 2015<br />Florian Corzilius, Gereon Kremer, Sebastian Junges,<br />Stefan Schupp, Erika Abraham</p></html>";
    public static final String PATH_ICON_ABOUT = IOTools.SMTRAT_GRAPHICS_DIR + File.separator + "logoBig.png";
    public static final String PATH_ICON_GUI = IOTools.SMTRAT_GRAPHICS_DIR + File.separator + "icon.png";
    
    // Visualization
// VISUALIZATION_HEIGHT to be changed
    public static final int VISUALIZATION_HEIGHT = 500;
// VISUALIZATION_PADDING to be changed
    public static final int VISUALIZATION_PADDING = 50;
// VISUALIZATION_WIDTH to be changed
    public static final int VISUALIZATION_WIDTH = 750;
    
    // Edge
    public static final Color EDGE_COLOR = Color.LIGHT_GRAY;
    public static final double EDGE_QUAD_CURVE_OFFSET = 50.0d;
    
    // Edge label
    private static final double EDGE_LABEL_CLOSENESS = 0.5d;
    private static final int TOOL_TIP_TEXT_WIDTH_IN_CHARS = 80;
    
    // Vertex
    private static final float VERTEX_PICKED_STROKE_WIDTH = 1.75f;

    // Menu items
    private final JMenuItem newMenuItem, openMenuItem, saveMenuItem, saveAsMenuItem, exitMenuItem, manageSolversMenuItem, takeScreenshotMenuItem, instructionsMenuItem, licenseMenuItem, aboutMenuItem;

    // Graph datastructure and graph visualization
    private final FRLayout<Vertex,Edge> layout;
    private final VisualizationViewer<Vertex,Edge> visualization;
    private StrategyGraph graph;
    private File graphFile;
    private String solverName;
    
    private GUI()
    {
        super( TITLE );

        graph = new StrategyGraph();
        graphFile = null;
        solverName = null;

        // Layout
        layout = new FRLayout( graph, new Dimension( VISUALIZATION_WIDTH-VISUALIZATION_PADDING, VISUALIZATION_HEIGHT-VISUALIZATION_PADDING ) );
        layout.setLocation( graph.getRoot(), VISUALIZATION_PADDING, VISUALIZATION_HEIGHT/2 );
        layout.lock( graph.getRoot(), true );
        
        // Visualization
        visualization = new VisualizationViewer( layout, new Dimension( VISUALIZATION_WIDTH, VISUALIZATION_HEIGHT ) );
        visualization.setBackground( Color.WHITE );
        visualization.addChangeListener( new ChangeListener()
        {
            @Override
            public void stateChanged( ChangeEvent ce )
            {
                saveMenuItem.setEnabled( true );
            }
        });

        // Edge
        Transformer<Context<Graph<Vertex,Edge>,Edge>,Shape> est = new Transformer<Context<Graph<Vertex,Edge>,Edge>,Shape>()
        {
            @Override
            public Shape transform( Context<Graph<Vertex,Edge>,Edge> c )
            {
                Vertex v1 = c.graph.getEndpoints( c.element ).getFirst();
                Vertex v2 = c.graph.getEndpoints( c.element ).getSecond();
                if ( c.graph.getSuccessors( v2 ).contains( v1 ) )
                {
                    return new QuadCurve2D.Double( 0.0d, 0.0d, 0.5d, EDGE_QUAD_CURVE_OFFSET, 1.0d, 0.0d );
                }
                else
                {
                    return new QuadCurve2D.Double( 0.0d, 0.0d, 0.0d, 0.0d, 1.0d, 0.0d );
                }
            }
        };
        visualization.getRenderContext().setEdgeShapeTransformer( est );
        visualization.getRenderContext().setEdgeDrawPaintTransformer( new ConstantTransformer( EDGE_COLOR ) );
        
        // EdgeLabel
        Transformer<MouseEvent,String> mett = new Transformer<MouseEvent,String>()
        {
            @Override
            public String transform( MouseEvent me )
            {
                Point p = me.getPoint();
                Edge e;
                if( (e = graph.getEdge( p ))!=null )
                {
                    StringBuilder ret = new StringBuilder();
                    ret.append( "<html><p>" );
                    int sum = 0;
                    Condition condition = e.getCondition();
                    for( int i=0; i<condition.size(); i++ )
                    {
                        sum += condition.getLength( i );
                        if( sum>TOOL_TIP_TEXT_WIDTH_IN_CHARS )
                        {
                            ret.append( "<br />" );
                            sum = condition.getLength( i );
                        }
                        ret.append( condition.getValue( i ) );
                    }
                    ret.append( "</p></html>" );
                    return ret.toString();
                }
                visualization.repaint();
                return null;
            }
        };
        visualization.setMouseEventToolTipTransformer( mett ); 
        visualization.getRenderer().setEdgeLabelRenderer( new EdgeLabelRendering() );
        visualization.getRenderContext().setEdgeLabelTransformer( new ToStringLabeller() );
        visualization.getRenderContext().setEdgeLabelRenderer( new DefaultEdgeLabelRenderer( Color.BLACK, false ) );
        visualization.getRenderContext().setEdgeLabelClosenessTransformer( new ConstantDirectionalEdgeValueTransformer( EDGE_LABEL_CLOSENESS, EDGE_LABEL_CLOSENESS ) );
        
        // Vertex
        Transformer<Vertex,Stroke> vst = new Transformer<Vertex,Stroke>()
        {
            @Override
            public Stroke transform( Vertex vertex )
            {
                PickedState<Vertex> pvs = visualization.getPickedVertexState();
                if ( pvs.isPicked( vertex ) )
                {
                    return new BasicStroke( VERTEX_PICKED_STROKE_WIDTH );
                }
                else
                {
                    return new BasicStroke();
                }
            }
        };
        visualization.getRenderContext().setVertexStrokeTransformer( vst );
        
        // VertexLabel
        visualization.getRenderContext().setVertexLabelTransformer( new ToStringLabeller() );

        // Mouse
        PluggableGraphMouse graphMouse = new PluggableGraphMouse();
        graphMouse.add( new PickingGraphMousePlugin( GUI.this ) );        
        graphMouse.add( new EditingGraphMousePlugin( GUI.this ) );
        visualization.setGraphMouse( graphMouse );
        
        try
        {
            IOTools.initialize( GUI.this, layout );
        }
        catch( IOTools.IOToolsException ex )
        {
            System.err.println( ex.getMessage() );
        }

        JMenuBar menuBar = new JMenuBar();
        MenuBarAction menuBarAction = new MenuBarAction();

        JMenu fileMenu = new JMenu( "File" );
        fileMenu.setMnemonic( KeyEvent.VK_F );
        newMenuItem = new JMenuItem( "New" );
        newMenuItem.addActionListener( menuBarAction );
        newMenuItem.setMnemonic( KeyEvent.VK_N );
        newMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_N, KeyEvent.CTRL_DOWN_MASK ) );
        openMenuItem = new JMenuItem( "Open" );
        openMenuItem.addActionListener( menuBarAction );
        openMenuItem.setMnemonic( KeyEvent.VK_O );
        openMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_O, KeyEvent.CTRL_DOWN_MASK ) );
        saveMenuItem = new JMenuItem( "Save" );
        saveMenuItem.addActionListener( menuBarAction );
        saveMenuItem.setEnabled( false );
        saveMenuItem.setMnemonic( KeyEvent.VK_S );
        saveMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_S, KeyEvent.CTRL_DOWN_MASK ) );
        saveAsMenuItem = new JMenuItem( "Save As..." );
        saveAsMenuItem.addActionListener( menuBarAction );
        saveAsMenuItem.setMnemonic( KeyEvent.VK_V );
        saveAsMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_S, KeyEvent.SHIFT_MASK+KeyEvent.CTRL_MASK ) );
        exitMenuItem = new JMenuItem( "Exit" );
        exitMenuItem.addActionListener( menuBarAction );
        exitMenuItem.setMnemonic( KeyEvent.VK_X );
        fileMenu.add( newMenuItem );
        fileMenu.add( openMenuItem );
        fileMenu.addSeparator();
        fileMenu.add( saveMenuItem );
        fileMenu.add( saveAsMenuItem );
        fileMenu.addSeparator();
        fileMenu.add( exitMenuItem );
        menuBar.add( fileMenu );
        
        JMenu toolsMenu = new JMenu( "Tools" );
        toolsMenu.setMnemonic( KeyEvent.VK_T );
        manageSolversMenuItem = new JMenuItem( "Manage Solvers " );
        manageSolversMenuItem.addActionListener( menuBarAction );
        manageSolversMenuItem.setMnemonic( KeyEvent.VK_M );
        manageSolversMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_F5, 0 ) );
        takeScreenshotMenuItem = new JMenuItem( "Take Screenshot" );
        takeScreenshotMenuItem.addActionListener( menuBarAction );
        takeScreenshotMenuItem.setMnemonic( KeyEvent.VK_A );
        takeScreenshotMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_F6, 0 ) );
        toolsMenu.add( manageSolversMenuItem );
        toolsMenu.addSeparator();
        toolsMenu.add( takeScreenshotMenuItem );
        menuBar.add( toolsMenu );

        JMenu helpMenu = new JMenu( "Help" );
        helpMenu.setMnemonic( KeyEvent.VK_H );
        instructionsMenuItem = new JMenuItem( "Instructions" );
        instructionsMenuItem.addActionListener( menuBarAction );
        instructionsMenuItem.setMnemonic( KeyEvent.VK_I );
        instructionsMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_F1, 0 ) );
        licenseMenuItem = new JMenuItem( "License" );
        licenseMenuItem.addActionListener( menuBarAction );
        licenseMenuItem.setMnemonic( KeyEvent.VK_L );
        licenseMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_F2, 0 ) );
        aboutMenuItem = new JMenuItem( "About" );
        aboutMenuItem.addActionListener( menuBarAction );
        aboutMenuItem.setMnemonic( KeyEvent.VK_A );
        aboutMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_F3, 0 ) );
        helpMenu.add( instructionsMenuItem );
        helpMenu.add( licenseMenuItem );
        helpMenu.add( aboutMenuItem );
        menuBar.add( helpMenu );

        setJMenuBar( menuBar );
        
        add( visualization );
        addWindowListener( GUI.this );
        pack();
        setDefaultCloseOperation( JFrame.DO_NOTHING_ON_CLOSE );
        setIconImage( new ImageIcon( PATH_ICON_GUI ).getImage() );
        Dimension screensize = Toolkit.getDefaultToolkit().getScreenSize();
        setLocation( (screensize.width-this.getWidth())/2, (screensize.height-this.getHeight())/2 );
        setResizable( false );
        setVisible( true );
    }
    
    public VisualizationViewer getVisualization()
    {
        return visualization;
    }
    
    public void openInstructions()
    {
        instructionsMenuItem.doClick();
    }
    
    public static void main( String[] args )
    {
        GUI gui = new GUI();
    }

    @Override
    public void windowActivated( WindowEvent we ){}
    
    @Override
    public void windowClosed( WindowEvent we ){}

    @Override
    public void windowClosing( WindowEvent we )
    {
        if( !checkForUnsavedChanges() )
        {
            return;
        }
        setVisible( false );
        dispose();
        System.exit( 0 );
    }
    
    @Override
    public void windowDeactivated( WindowEvent we ){}

    @Override
    public void windowDeiconified( WindowEvent we ){}

    @Override
    public void windowIconified( WindowEvent we ){}

    @Override
    public void windowOpened( WindowEvent we ){}

    private boolean checkForUnsavedChanges()
    {
        if( saveMenuItem.isEnabled() )
        {
            // Escape = -1, Yes = 0, No = 1, Cancel = 2
            int choice = JOptionPane.showConfirmDialog( GUI.this, "Strategy has been modified. Save changes?", "Question", JOptionPane.YES_NO_CANCEL_OPTION );
            if( choice==-1 || choice==2 )
            {
                return false;
            }
            else if( choice==0 )
            {
                if( IOTools.saveGraph( graphFile, false )==null )
                {
                    return false;
                }
            }
            return true;
        }
        else
        {
            return true;
        }
    }
    
    private class MenuBarAction extends AbstractAction
    {
        @Override
        public void actionPerformed( ActionEvent ae )
        {
            try
            {
                if( ae.getSource()==newMenuItem )
                {
                    if( !checkForUnsavedChanges() )
                    {
                        return;
                    }
                    graph = new StrategyGraph();
                    graphFile = null;
                    solverName = null;
                    layout.setGraph( graph );
// Replace VISUALIZATION_HEIGHT/2 by visualization.getHeight()/2 if GUI is resizable or scrollable
                    layout.setLocation( graph.getRoot(), VISUALIZATION_PADDING, VISUALIZATION_HEIGHT/2 );
                    layout.lock( graph.getRoot(), true );
                    visualization.repaint();
                    saveMenuItem.setEnabled( false );
                }
                else if( ae.getSource()==openMenuItem )
                {
                    if( !checkForUnsavedChanges() )
                    {
                        return;
                    }
                    File fp = IOTools.openGraph();
                    if( fp!=null )
                    {
                        graphFile = fp;
                        graph = (StrategyGraph) layout.getGraph();
                        visualization.repaint();
                        saveMenuItem.setEnabled( false );
                    }
                }
                else if( ae.getSource()==saveMenuItem || ae.getSource()==saveAsMenuItem )
                {
                    File fp = IOTools.saveGraph( graphFile, ae.getSource()==saveAsMenuItem );
                    if( fp!=null )
                    {
                        graphFile = fp;
                        saveMenuItem.setEnabled( false );
                    }
                }
                else if( ae.getSource()==exitMenuItem )
                {
                    windowClosing( null );
                }
                else if( ae.getSource()==manageSolversMenuItem )
                {
                    if( solverName==null && graphFile!=null )
                    {
                        solverName = graphFile.getPath().substring( graphFile.getPath().lastIndexOf( File.separator )+1 );
                        solverName = solverName.substring( 0, solverName.length()-4 );
                    }
                    
                    String newSolverName = ManageSolverDialog.showDialog( GUI.this, solverName );
                    if( newSolverName!=null )
                    {
                        solverName = newSolverName;
                    }
                }
                else if( ae.getSource()==takeScreenshotMenuItem )
                {
                    IOTools.saveScreenshot();
                }
                else if( ae.getSource()==instructionsMenuItem )
                {
                    try
                    {
                        Config config = new Config();
                        File file = new File(config.getManualPath());
                        String os = System.getProperty("os.name").toLowerCase();
                        boolean isWindows = os.contains("win");
                        boolean isLinux = os.contains("nux") || os.contains("nix");
                        boolean isMac = os.contains("mac");
                        if (isWindows)
                        {
                            Runtime.getRuntime().exec(new String[]
                            {"rundll32", "url.dll,FileProtocolHandler",
                             file.getAbsolutePath()});
                        }
                        else if (isLinux || isMac)
                        {
                            Runtime.getRuntime().exec(new String[]{"/usr/bin/open", file.getAbsolutePath()});
                        }
                        else
                        {
                            // Unknown OS, try with desktop
                            if (Desktop.isDesktopSupported())
                            {
                                Desktop.getDesktop().open(file);
                            }
                            else
                            {
                                System.out.println( "Cannot open manual." );
                            }
                        }
                    }
                    catch (Exception e)
                    {
                        e.printStackTrace(System.err);
                        System.out.println( "Cannot open manual." );
                    }
                }
                else if( ae.getSource()==licenseMenuItem )
                {
                    LicenseDialog.showDialog( GUI.this );
                }
                else if( ae.getSource()==aboutMenuItem )
                {
                    JOptionPane.showMessageDialog( GUI.this, HTML_ABOUT, "About " + TITLE, JOptionPane.INFORMATION_MESSAGE, new ImageIcon( PATH_ICON_ABOUT ) );
                }
            }
            catch( Exception ex )
            {
                JOptionPane.showMessageDialog( GUI.this, ex.toString(), "Error", JOptionPane.ERROR_MESSAGE );
            }
        }
    }
}