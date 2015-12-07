import edu.uci.ics.jung.algorithms.layout.FRLayout;
import java.awt.HeadlessException;
import java.awt.Rectangle;
import java.awt.image.BufferedImage;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.imageio.ImageIO;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.filechooser.FileFilter;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.w3c.dom.Text;
import org.xml.sax.SAXException;

/**
 * @file IOTools.java
 *       - needs SMT-RAT
 *
 * @author  Henrik Schmitz
 * @since   2012-02-07
 * @version 2013-01-18
 */
public class IOTools
{
    private static final File SMTRAT_BASE_DIR = new File( ".." + File.separator + ".." + File.separator + ".." + File.separator );
    public static final File SMTRAT_GRAPHICS_DIR = new File( SMTRAT_BASE_DIR + File.separator + "htdocs" + File.separator + "images" );
    private static final File SMTRAT_SOURCE_DIR = new File( SMTRAT_BASE_DIR + File.separator + "src" + File.separator + "lib" );
    private static final File SMTRAT_STRATEGIES_DIR = new File( SMTRAT_SOURCE_DIR + File.separator + "strategies" );

    private static final String CONDITION_CLASS = "Condition";
    public static final String STRATEGIES_HEADER_CLASS = "strategies";

    private static final String MODULES_DIRECTORY = SMTRAT_SOURCE_DIR + File.separator + "modules";
    private static final File PROPOSITION_SOURCE_FILE = new File( getAbsoluteCarlPath() + File.separator + "carl" + File.separator + "formula" + File.separator + "Condition.h" );
    private static final File SMTRAT_STRATEGIES_BUILD_FILE = new File( SMTRAT_STRATEGIES_DIR + File.separator + "CMakeLists.txt" );
    private static final File SMTRAT_STRATEGIES_HEADER_FILE = new File( SMTRAT_STRATEGIES_DIR + File.separator + STRATEGIES_HEADER_CLASS + ".h" );

    private static final String TAB = "    ";
    private static final String NL = System.lineSeparator();

    public static final ArrayList<Module> modules = readModules();
    public static final String longestModuleName = getLongestModuleName( modules );
    public static final String longestSettingName = getLongestSettingName( modules );
    public static final ArrayList<String> propositions = readPropositions();
    public static final ArrayList<String> existingSolverNames = readExistingSolverNames();

    private static GUI gui;
    public static FRLayout layout;

    public static String deleteSolver( String solverName )
    {
        return manageSolvers( solverName, false );
    }

    public static String exportSolver( String solverName )
    {
        return manageSolvers( solverName, true );
    }

    public static void initialize( GUI gui, FRLayout layout ) throws IOToolsException
    {
        IOTools.gui = gui;
        IOTools.layout = layout;

        if( !SMTRAT_BASE_DIR.exists() )
        {
            throw new IOToolsException( IOToolsException.SMTRAT_BASE_DIR_EXCEPTION );
        }
        if( !SMTRAT_GRAPHICS_DIR.exists() )
        {
            throw new IOToolsException( IOToolsException.SMTRAT_GRAPHICS_DIR_EXCEPTION );
        }
        if( !SMTRAT_SOURCE_DIR.exists() )
        {
            throw new IOToolsException( IOToolsException.SMTRAT_SOURCE_DIR_EXCEPTION );
        }

        if( modules==null )
        {
            throw new IOToolsException( IOToolsException.MODULES_PARSE_EXCEPTION );
        }
        if( propositions==null )
        {
            throw new IOToolsException( IOToolsException.PROPOSITIONS_PARSE_EXCEPTION );
        }
    }

    public static File openGraph()
    {
        try
        {
            JFileChooser fileChooser = new JFileChooser();
            fileChooser.setDialogTitle( "Open" );
            fileChooser.removeChoosableFileFilter( fileChooser.getChoosableFileFilters()[0] );
            fileChooser.setFileFilter( new XMLFilter() );
            fileChooser.setMultiSelectionEnabled( false );
            fileChooser.setCurrentDirectory( SMTRAT_STRATEGIES_DIR );
            while( true )
            {
                int option = fileChooser.showOpenDialog( gui );
                if( option==JFileChooser.APPROVE_OPTION )
                {
                    File graphFile = fileChooser.getSelectedFile();
                    if( !graphFile.getPath().toLowerCase().endsWith( ".xml" ) )
                    {
                        graphFile = new File( graphFile.getPath() + ".xml" );
                        fileChooser.setSelectedFile( graphFile );
                    }
                    if( !fileChooser.getSelectedFile().canRead() )
                    {
                        JOptionPane.showMessageDialog( gui, "Permission denied. Please select a different file.", "Information", JOptionPane.INFORMATION_MESSAGE );
                        continue;
                    }
                    else
                    {
                        createGraph( graphFile );
                        return graphFile;
                    }
                }
                else if( option==JFileChooser.CANCEL_OPTION )
                {
                    return null;
                }
                else
                {
                    JOptionPane.showMessageDialog( gui, "An error occured while opening the Strategy file.", "Error", JOptionPane.ERROR_MESSAGE );
                    return null;
                }
            }

        }
        catch( HeadlessException | IOException | ParserConfigurationException | SAXException | IOToolsException ex )
        {
            JOptionPane.showMessageDialog( gui, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
            return null;
        }
    }

    public static File saveGraph( File graphFile, boolean saveAs )
    {
        try
        {
            if( graphFile==null || saveAs )
            {
                JFileChooser fileChooser = new JFileChooser();
                if( saveAs )
                {
                    fileChooser.setDialogTitle( "Save As..." );
                }
                else
                {
                    fileChooser.setDialogTitle( "Save" );
                }
                fileChooser.removeChoosableFileFilter( fileChooser.getChoosableFileFilters()[0] );
                fileChooser.setFileFilter( new XMLFilter() );
                fileChooser.setMultiSelectionEnabled( false );
                fileChooser.setCurrentDirectory( SMTRAT_STRATEGIES_DIR );
                while( true )
                {
                    int option = fileChooser.showSaveDialog( gui );
                    if( option==JFileChooser.APPROVE_OPTION )
                    {
                        graphFile = fileChooser.getSelectedFile();
                        if( !graphFile.getPath().toLowerCase().endsWith(".xml") )
                        {
                            graphFile = new File( graphFile.getPath() + ".xml" );
                            fileChooser.setSelectedFile( graphFile );
                        }
                        if( fileChooser.getSelectedFile().exists() )
                        {
                            // Escape = -1, Yes = 0, No = 1, Cancel = 2
                            int choice = JOptionPane.showConfirmDialog( gui, "File already exists. Overwrite file?", "Question", JOptionPane.YES_NO_CANCEL_OPTION );
                            if( choice==-1 || choice==2 )
                            {
                                return null;
                            }
                            else if( choice==0 )
                            {
                                break;
                            }
                        }
                        else if( !fileChooser.getCurrentDirectory().canWrite() )
                        {
                            JOptionPane.showMessageDialog( gui, "Permission denied. Please select a different location.", "Information", JOptionPane.INFORMATION_MESSAGE );
                        }
                        else
                        {
                            break;
                        }
                    }
                    else if( option==JFileChooser.CANCEL_OPTION )
                    {
                        return null;
                    }
                    else
                    {
                        JOptionPane.showMessageDialog( gui, "An error occured while saving the Strategy file.", "Error", JOptionPane.ERROR_MESSAGE );
                        return null;
                    }
                }
            }
            createXML( graphFile );
            return graphFile;
        }
        catch( HeadlessException | TransformerException | ParserConfigurationException ex )
        {
            JOptionPane.showMessageDialog( gui, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
            return null;
        }
    }

    public static void saveScreenshot()
    {
        try
        {
            JFileChooser fileChooser = new JFileChooser();
            fileChooser.setDialogTitle( "Save Screenshot" );
            fileChooser.removeChoosableFileFilter( fileChooser.getChoosableFileFilters()[0] );
            fileChooser.setFileFilter( new PNGFilter() );
            fileChooser.setMultiSelectionEnabled( false );
            fileChooser.setCurrentDirectory( SMTRAT_STRATEGIES_DIR );
            while( true )
            {
                int option = fileChooser.showSaveDialog( gui );
                if( option==JFileChooser.APPROVE_OPTION )
                {
                    String screenshotFilePath = fileChooser.getSelectedFile().getPath();
                    if( !screenshotFilePath.toLowerCase().endsWith(".png") )
                    {
                        screenshotFilePath += ".png";
                        fileChooser.setSelectedFile( new File( screenshotFilePath ) );
                    }
                    if( fileChooser.getSelectedFile().exists() )
                    {
                        // Escape = -1, Yes = 0, No = 1, Cancel = 2
                        int choice = JOptionPane.showConfirmDialog( gui, "File already exists. Overwrite file?", "Question", JOptionPane.YES_NO_CANCEL_OPTION );
                        if( choice==-1 || choice==2 )
                        {
                            return;
                        }
                        else if( choice==0 )
                        {
                            break;
                        }
                    }
                    else if( !fileChooser.getCurrentDirectory().canWrite() )
                    {
                        JOptionPane.showMessageDialog( gui, "Permission denied. Please select a different location.", "Information", JOptionPane.INFORMATION_MESSAGE );
                    }
                    else
                    {
                        break;
                    }
                }
                else if( option==JFileChooser.CANCEL_OPTION )
                {
                    return;
                }
                else
                {
                    JOptionPane.showMessageDialog( gui, "An error occured while saving the screenshot.", "Error", JOptionPane.ERROR_MESSAGE );
                    return;
                }
            }
            Rectangle rectangle = gui.getVisualization().getBounds();
            BufferedImage bufferedImage = new BufferedImage( rectangle.width, rectangle.height, BufferedImage.TYPE_INT_ARGB );
            gui.getVisualization().paint( bufferedImage.getGraphics() );
            ImageIO.write( bufferedImage, "png", fileChooser.getSelectedFile() );
        }
        catch( HeadlessException | IOException ex )
        {
            JOptionPane.showMessageDialog( gui, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
        }
    }

    private static void createGraph( File graphFile ) throws IOException, ParserConfigurationException, SAXException, IOToolsException
    {
        StrategyGraph graph = new StrategyGraph();
        HashMap<Integer,Vertex> vertices = new HashMap();

        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = dbf.newDocumentBuilder();
        Document document = db.parse( graphFile.getPath() );

        Element rootElement = document.getDocumentElement();
        if( !rootElement.getTagName().equals( "graph" ) )
        {
            throw new IOToolsException( IOToolsException.XML_EXCEPTION );
        }

        Element verticesElement = (Element) rootElement.getFirstChild();
        if( !verticesElement.getTagName().equals( "vertices" ) )
        {
            throw new IOToolsException( IOToolsException.XML_EXCEPTION );
        }

        NodeList vertexNodeList = verticesElement.getChildNodes();
        for( int i=0; i<vertexNodeList.getLength(); i++ )
        {
            Element vertexElement = (Element) vertexNodeList.item( i );
            if( !vertexElement.getTagName().equals( "vertex" ) )
            {
                throw new IOToolsException( IOToolsException.XML_EXCEPTION );
            }

            Element moduleElement = (Element) vertexElement.getFirstChild();
            if( !moduleElement.getTagName().equals( "module" ) )
            {
                throw new IOToolsException( IOToolsException.XML_EXCEPTION );
            }

            Element nameElement = (Element) moduleElement.getFirstChild();
            if( !nameElement.getTagName().equals( "name" ) )
            {
                throw new IOToolsException( IOToolsException.XML_EXCEPTION );
            }

            Element settingElement = (Element) moduleElement.getLastChild();
            if( !settingElement.getTagName().equals( "setting" ) )
            {
                throw new IOToolsException( IOToolsException.XML_EXCEPTION );
            }

            int id;
            double x, y;
            try
            {
                id = new Integer( vertexElement.getAttributes().getNamedItem( "id" ).getNodeValue() );
                x = new Double( vertexElement.getAttributes().getNamedItem( "positionX" ).getNodeValue() );
                y = new Double( vertexElement.getAttributes().getNamedItem( "positionY" ).getNodeValue() );
            }
            catch( RuntimeException ex )
            {
                throw new IOToolsException( IOToolsException.XML_EXCEPTION );
            }
            String name = ((Text) nameElement.getFirstChild()).getData();
            String settingName = ((Text) settingElement.getFirstChild()).getData();
            Vertex vertex;
            if( name.equals( StrategyGraph.ROOT_VERTEX_MODULE_NAME ) )
            {
                vertex = graph.getRoot();
            }
            else
            {
                Module module = null;
                for( Module m : modules )
                {
                    if( m.getName().equals( name ) )
                    {
                        module = m;
                        break;
                    }
                }
                if( module == null )
                    throw new IOToolsException( IOToolsException.XML_EXCEPTION );
                if( !settingName.equals("None") )
                {
                    int ret = module.changeChosenSetting( settingName );
                    if( ret == -1 )
                        throw new IOToolsException( IOToolsException.XML_EXCEPTION );
                }
                vertex = new Vertex( module );
                graph.addVertex( vertex );
            }
            layout.setLocation( vertex, x, y);
            vertices.put( id, vertex );
        }

        Element edgesElement = (Element) rootElement.getLastChild();
        if( !edgesElement.getTagName().equals( "edges" ) )
        {
            throw new IOToolsException( IOToolsException.XML_EXCEPTION );
        }

        int priorityAllocator = 0;
        NodeList edgeNodeList = edgesElement.getChildNodes();
        for( int i=0; i<edgeNodeList.getLength(); i++ )
        {
            Element edgeElement = (Element) edgeNodeList.item( i );
            if( !edgeElement.getTagName().equals( "edge" ) )
            {
                throw new IOToolsException( IOToolsException.XML_EXCEPTION );
            }

            Element conditionElement = (Element) edgeElement.getFirstChild();
            if( !conditionElement.getTagName().equals( "condition" ) )
            {
                throw new IOToolsException( IOToolsException.XML_EXCEPTION );
            }

            Element priorityElement = (Element) edgeElement.getLastChild();
            if( !priorityElement.getTagName().equals( "priority" ) )
            {
                throw new IOToolsException( IOToolsException.XML_EXCEPTION );
            }

            boolean backLink;
            int destination, source;
            try
            {
                backLink = Boolean.valueOf( edgeElement.getAttributes().getNamedItem( "backLink" ).getNodeValue() );
                destination = new Integer( edgeElement.getAttributes().getNamedItem( "destination" ).getNodeValue() );
                source = new Integer( edgeElement.getAttributes().getNamedItem( "source" ).getNodeValue() );
            }
            catch( RuntimeException ex )
            {
                throw new IOToolsException( IOToolsException.XML_EXCEPTION );
            }

            Condition condition = new Condition();
            Element valueElement = (Element) conditionElement.getFirstChild();
            while( valueElement!=null )
            {
                if( !valueElement.getTagName().equals( "value" ) || condition.addElement( ((Text) valueElement.getFirstChild()).getData() ).equals( "" ) )
                {
                    throw new IOToolsException( IOToolsException.XML_EXCEPTION );
                }
                valueElement = (Element) valueElement.getNextSibling();
            }
            int priority = new Integer( ((Text) priorityElement.getLastChild()).getData() );
            priorityAllocator = Math.max( priority, priorityAllocator );
            Edge edge = new Edge( condition, backLink, priority );
            graph.addEdge( edge, vertices.get( source ), vertices.get( destination) );
        }
        StrategyGraph.priorityAllocator = ++priorityAllocator;
        layout.setGraph( graph );
    }

    private static void createXML( File graphFilePath ) throws TransformerConfigurationException, TransformerException, ParserConfigurationException
    {
        StrategyGraph graph = (StrategyGraph) layout.getGraph();
        HashMap<Vertex,Integer> ids = new HashMap();
        Integer id = 0;

        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = dbf.newDocumentBuilder();
        Document document = db.newDocument();

        Element rootElement = document.createElement( "graph" );
        document.appendChild( rootElement );

        Element verticesElement = document.createElement( "vertices" );
        rootElement.appendChild( verticesElement );

        Collection<Vertex> vertices = graph.getVertices();
        for( Vertex v : vertices )
        {
            ids.put( v, id );
            Element vertexElement = document.createElement( "vertex" );
            vertexElement.setAttribute( "id", (id++).toString() );
            Double x = new Double( layout.getX( v ) );
            vertexElement.setAttribute( "positionX", x.toString() );
            Double y = new Double( layout.getY( v ) );
            vertexElement.setAttribute( "positionY", y.toString() );
            verticesElement.appendChild( vertexElement );

            Element moduleElement = document.createElement( "module" );
            vertexElement.appendChild( moduleElement );

            Element nameElement = document.createElement( "name" );
            nameElement.appendChild( document.createTextNode( v.getModule().getName() ) );
            moduleElement.appendChild( nameElement );

            Element settingElement = document.createElement( "setting" );
            String curset = v.getModule().currentSetting();
            if( curset == null )
                curset = "None";
            settingElement.appendChild( document.createTextNode( curset ) );
            moduleElement.appendChild( settingElement );
        }

        Element edgesElement = document.createElement( "edges" );
        rootElement.appendChild( edgesElement );

        Collection<Edge> edges = graph.getEdges();
        if( !edges.isEmpty() )
        {
            for( Edge e : edges )
            {
                Element edgeElement = document.createElement( "edge" );
                Boolean backLink = e.isBackLink();
                edgeElement.setAttribute( "backLink" , backLink.toString() );
                id = ids.get( (Vertex) graph.getEndpoints( e ).getSecond() );
                edgeElement.setAttribute( "destination" , id.toString() );
                id = ids.get( (Vertex) graph.getEndpoints( e ).getFirst() );
                edgeElement.setAttribute( "source", id.toString() );
                edgesElement.appendChild( edgeElement );

                Element conditionElement = document.createElement( "condition" );
                Condition condition = e.getCondition();
                for( int i=0; i<condition.size(); i++ )
                {
                    Element valueElement = document.createElement( "value" );
                    valueElement.appendChild( document.createTextNode( condition.getValueXML( i ) ) );
                    conditionElement.appendChild( valueElement );
                }
                edgeElement.appendChild( conditionElement );

                Element priorityElement = document.createElement( "priority" );
                Integer priority = e.getPriority();
                priorityElement.appendChild( document.createTextNode( priority.toString() ) );
                edgeElement.appendChild( priorityElement );
            }
        }

        TransformerFactory transformerFactory = TransformerFactory.newInstance();
        Transformer transformer = transformerFactory.newTransformer();
        DOMSource source = new DOMSource( document );
        StreamResult result = new StreamResult( graphFilePath );
        transformer.transform( source, result );
    }

    /**
     * Write newly created solver to the source incrementally and non-destructively.
     *
     * In particular, create new files for new solvers, and keep existing files for existing solvers. Do not delete solvers.
     *
     * @param name name of the solver
     * @param strategy
     * @param add If this flag is true, the respective solver is added to the source. Otherwise it is deleted.
     */
    private static String manageSolvers( String solverName, boolean add )
    {
        try
        {
            if( solverName==null || solverName.equals( "" ) || solverName.contains( "config" ) )
                return null;

            String solverNameUpperCase = solverName.toUpperCase();

            File headerFile = new File( SMTRAT_STRATEGIES_DIR.getPath() + File.separator + solverName + ".h" );
            File headerTempFile = null;
            File smtratStrategiesBuildTempFile = new File( SMTRAT_STRATEGIES_BUILD_FILE.getPath() + "~" );
            File smtratStrategiesHeaderTempFile = new File( SMTRAT_STRATEGIES_HEADER_FILE.getPath() + "~" );

            // Collect the string to implement the strategy of this solver and the string implementing the conditions the strategy uses.
            if( add )
            {
                StrategyGraph graph = (StrategyGraph) layout.getGraph();
                StringBuilder headerString = new StringBuilder();

                Collection<String> necessaryIdentifier = new ArrayList<String>();
                Collection<Edge> backlinks = new ArrayList<Edge>();
                Collection<String> conditions = new ArrayList<String>();
                Collection<String> moduleNames = new ArrayList<String>();
                getGraphInformation( graph, graph.getRoot(), necessaryIdentifier, backlinks, conditions, moduleNames );
                String graphString = getGraphString( graph, graph.getRoot(), new String( TAB + TAB + TAB ), necessaryIdentifier );
                
                // Write the content to the header file.
                // Write the preamble.
                headerString.append( "/**" + NL + 
                                     " * @file " + solverName + ".h" + NL +
                                     " */" + NL +
                                     "#pragma once" + NL + NL +
                                     "#include \"../solver/Manager.h\"" + NL );
                // Include all necessary modules.
                for( String moduleName : moduleNames )
                    headerString.append( "#include \"../modules/" + moduleName + "/" + moduleName + ".h\"" + NL );
                headerString.append( NL ); 
                // Write the solver class.
                headerString.append( "namespace smtrat" + NL + 
                                     "{" + NL );
                headerString.append( TAB + "/**" + NL +
                                     TAB + " * Strategy description." + NL +
                                     TAB + " *" + NL +
                                     TAB + " * @author" + NL +
                                     TAB + " * @since" + NL +
                                     TAB + " * @version" + NL +
                                     TAB + " *" + NL +
                                     TAB + " */" + NL );
                headerString.append( TAB + "class " + solverName + ":" + NL +
                                     TAB + TAB + "public Manager" + NL +
                                     TAB + "{" + NL );
                // Add all conditions used in the strategy.
                for( String condition : conditions )
                    headerString.append( condition + NL );
                headerString.append( TAB + TAB + "public:" + NL + NL +
                                     TAB + TAB + solverName + "(): Manager()" + NL + 
                                     TAB + TAB + "{" + NL );
                // Check if identifier have to added, which are used to create backlinks
                if( necessaryIdentifier.size() > 0 )
                {
                    headerString.append(  TAB + TAB + TAB + "size_t " );
                    int i = 0;
                    for( String ident : necessaryIdentifier )
                    {
                        headerString.append( ident + " = 0" );
                        if( i < necessaryIdentifier.size()-1 )
                            headerString.append( ", " );
                        ++i;
                    }
                    headerString.append( ";" + NL );
                }
                // Write the strategy of the solver.
                headerString.append( TAB + TAB + TAB + "setStrategy" );
                headerString.append( graphString );
                if( necessaryIdentifier.contains( graph.getRoot().identifier() ) )
                    headerString.append( ".id( " + graph.getRoot().identifier() + " )" );
                headerString.append( ";" + NL );
                // Add the backlinks.
                for( Edge bl : backlinks )
                {
                    Vertex from = (Vertex) graph.getSource( bl );
                    Vertex to = (Vertex) graph.getDest( bl );
                    headerString.append( TAB + TAB + TAB + "addEdge( " + from.identifier() + ", " + to.identifier() + " )" );
                    if( !bl.getCondition().isTrueCondition() )
                        headerString.append( ".condition( &conditionEvaluation" + bl.getPriority() + " )" );
                    headerString.append( ";" + NL );
                }
                headerString.append( TAB + TAB + "}" + NL +
                                     TAB + "};" + NL +
                                     "} // namespace smtrat" );

                // Try to store the content to the file.
                if( headerFile.exists() )
                {
                    headerTempFile = new File( headerFile.getPath() + "~" );
                    Files.copy( headerFile.toPath(), headerTempFile.toPath(), StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.COPY_ATTRIBUTES );
                }
                try( PrintWriter writeFile = new PrintWriter( new FileWriter( headerFile ) ) )
                {
                    writeFile.print( headerString.toString() );
                    writeFile.flush();
                }
                catch( Exception ex )
                {
                    if( headerTempFile!=null && headerTempFile.exists() )
                    {
                        Files.copy( headerTempFile.toPath(), headerFile.toPath(), StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.COPY_ATTRIBUTES );
                        Files.delete( headerTempFile.toPath() );
                    }
                    throw ex;
                }
            }

            if( headerTempFile!=null && headerTempFile.exists() )
                Files.delete( headerTempFile.toPath() );
            return solverName;
        }
        catch( IOException ex )
        {
            JOptionPane.showMessageDialog( gui, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
            return null;
        }
    }

    private static void getGraphInformation( StrategyGraph _graph, Vertex _vertex, Collection<String> _identifier, Collection<Edge> _backlinks, Collection<String> _conditions, Collection<String> _moduleNames )
    {
        Collection<Edge> outEdges = _graph.getOutEdges( _vertex );
        for( Edge outEdge : outEdges )
        {
            Vertex succ = (Vertex) _graph.getDest( outEdge );
            Condition condition = outEdge.getCondition();
            if( !condition.isTrueCondition() )
            {
                _conditions.add( 
                    TAB + TAB + "static bool conditionEvaluation" + outEdge.getPriority() + "( carl::Condition _condition )" + NL + 
                    TAB + TAB + "{" + NL +
                    TAB + TAB + TAB + "return " + "( " + condition.toStringCPP( "_condition" ) + " );" + NL + 
                    TAB + TAB + "}" + NL
                );
            }
            _moduleNames.add( succ.getModule().getName() );
            if( outEdge.isBackLink() )
            {
                _backlinks.add( outEdge );
                _identifier.add( _vertex.identifier() );
                _identifier.add(  succ.identifier() );
            }
            else
                getGraphInformation( _graph, succ, _identifier, _backlinks, _conditions, _moduleNames );
        }
    }

    private static String getGraphString( StrategyGraph _graph, Vertex _vertex, String _prefix, Collection<String> _necessaryIds )
    {
        Collection<Edge> outEdges = _graph.getOutEdges( _vertex );
        Collection<Edge> nonBacklingOutEdges = new ArrayList<Edge>();
        for( Edge outEdge : outEdges )
        {
            if( !outEdge.isBackLink() )
                nonBacklingOutEdges.add( outEdge );
        }
        if( nonBacklingOutEdges.isEmpty() )
            return "()";
        String result = new String( "(" + NL );
        result += _prefix + "{" + NL;
        int i = 0;
        for( Edge outEdge : nonBacklingOutEdges )
        {
            Condition condition = outEdge.getCondition();
            Vertex succ = (Vertex) _graph.getDest( outEdge );
            result += _prefix + TAB + "addBackend<" + succ.getModule().getNameAndSetting() + ">";
            result += getGraphString( _graph, succ, _prefix + TAB, _necessaryIds );
            if( !condition.isTrueCondition() )
                result += ".condition( &conditionEvaluation" + outEdge.getPriority() + " )";
            if( _necessaryIds.contains( succ.identifier() ) )
                result += ".id( " + succ.identifier() + " )";
            if( i < nonBacklingOutEdges.size()-1 )
                result += ",";
            result += NL;
            ++i;
        }
        result += _prefix + "})";
        return result;
    }

    /**
     * Scans the file ModuleTypes.h for potential modules. For each getType, the directory modules is searched for a class, derived from Module,
     * containing the module getType. The results of this search are returned.
     *
     * @return operational Modules available
     */
    private static ArrayList<Module> readModules()
    {
        ArrayList<Module> moduleList = new ArrayList<>();
        
        File file = new File( MODULES_DIRECTORY );
        String[] directories = file.list(new FilenameFilter()
        {
            @Override
            public boolean accept(File current, String name)
            {
                return new File(current, name).isDirectory();
            }
        });

        for( int i = 0; i < directories.length; ++i )
        {
            Module module = new Module( directories[i] );
            moduleList.add( module );

            String line;
            String settingPrefix = directories[i].substring( 0, directories[i].length() - 6 ) + "Settings";
            Pattern p = Pattern.compile("\\b"+settingPrefix, Pattern.CASE_INSENSITIVE);
            Collection<String> settings = new ArrayList<String>();
            String settingsFileName = MODULES_DIRECTORY + "/" + directories[i] + "/" + settingPrefix + ".h";
            try ( BufferedReader readFile = new BufferedReader( new FileReader( MODULES_DIRECTORY + "/" + directories[i] + "/" + settingPrefix + ".h" ) ) )
            {
                while( (line = readFile.readLine()) != null )
                {
                    if( line.indexOf("struct") != -1 )
                    {
                        Matcher m = p.matcher(line);

                        // indicate all matches on the line
                        if( m.find() )
                        {
                            String rem = line.substring( m.start(), line.length() ).split(" ")[0].replaceAll(":","");
                            settings.add( rem );
                        }
                    }
                }
            }
            catch( IOException ex )
            {
                // No Setting
            }
            for( String setting : settings  )
            {
                module.addSetting( setting );
            }
        }
        if( moduleList.isEmpty() )
            return null;
        else
        {
            Collections.sort( moduleList );
            return moduleList;
        }
    }

    private static String getLongestModuleName( ArrayList<Module> _modules )
    {
        String result = "";
        for( Module module : _modules )
        {
            if( module.getName().length() > result.length() )
                result = module.getName();
        }
        return result;
    }

    private static String getLongestSettingName( ArrayList<Module> _modules )
    {
        String result = "";
        for( Module module : _modules )
        {
            for( String setting : module.getSettings() )
            {
                if( setting.length() > result.length() )
                    result = setting;
            }
        }
        return result;
    }

    /**
     * Scans the file Condition.h for potential conditions.
     *
     * @return conditions usable in a strategy
     */
    private static ArrayList<String> readPropositions()
    {
        ArrayList<String> propositionList = new ArrayList<>();
        String[] fileContent = removeComments( PROPOSITION_SOURCE_FILE ).split( "static\\s*const\\s*" + CONDITION_CLASS + "\\s*" );

        if( fileContent.length==1 )
        {
            return null;
        }

        for( int i=1; i<fileContent.length; i++ )
        {
            int offset;
            String line = fileContent[i];
            if( line.startsWith( "PROP_" ) && (offset = line.indexOf( "=" ))!=-1 )
            {
                propositionList.add( line.substring( 5, offset ).trim() );
            }
        }

        if( propositionList.isEmpty() )
        {
            return null;
        }
        else
        {
            Collections.sort( propositionList );
            return propositionList;
        }
    }

    /**
     * Read the solvers available in the source.
     *
     * @param conditions
     * @return a map "Solver name" -> "Strategy"
     */
    private static ArrayList<String> readExistingSolverNames()
    {
        ArrayList<String> solverNamesList = new ArrayList<>();

        for( File f : SMTRAT_STRATEGIES_DIR.listFiles( new StrategyHeaderFilter() ) )
        {
            String name = f.getName();
            if( !name.contains( "config" ) )
            {
                name = name.substring( 0, name.length()-2 );
                solverNamesList.add( name );
            }
        }

        Collections.sort( solverNamesList );
        return solverNamesList;
    }
    
    private static String getAbsoluteCarlPath()
    {
        Config config = new Config();
        return config.getCarlSourcePath();
    }

    private static String removeComments( File file )
    {
        try ( BufferedReader readFile = new BufferedReader( new FileReader( file ) ) )
        {
            int offset;
            String line;
            StringBuilder ret = new StringBuilder();
            boolean commentClosed = true;
            while( (line = readFile.readLine())!=null )
            {
                if( !commentClosed )
                {
                    offset = line.indexOf( "*/" );
                    if( offset!=-1 )
                    {
                        line = line.substring( offset+2 );
                        commentClosed = true;
                    }
                    else
                    {
                        continue;
                    }
                }
                line = line.replaceAll( "/\\*.*\\*/", "" ).replaceAll( "//.*", "" );
                offset = line.indexOf( "/*" );
                if( offset!=-1 )
                {
                    line = line.substring( 0, offset );
                    commentClosed = false;
                }
                ret.append( line );
            }
            return ret.toString();
        }
        catch( IOException ex )
        {
            JOptionPane.showMessageDialog( gui, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
            return null;
        }
    }

    public static class IOToolsException extends Exception
    {
        public static final String BUILD_ENTRY_POINT_NOT_FOUND = "Warning: Could not find entry point in strategies build file " + SMTRAT_STRATEGIES_BUILD_FILE + ".";
        public static final String HEADER_ENTRY_POINT_NOT_FOUND = "Warning: Could not find entry point in strategies header file " + SMTRAT_STRATEGIES_HEADER_FILE + ".";
        public static final String MODULES_PARSE_EXCEPTION = "Warning: Could not parse any Modules.";
        public static final String MODULE_TYPE_LISTING_FILE_EXCEPTION = MODULES_PARSE_EXCEPTION + " Module Type listing file not found.";
        public static final String PROPOSITIONS_PARSE_EXCEPTION = "Warning: Could not parse Propositions from source file.";
        public static final String SMTRAT_BASE_DIR_EXCEPTION = "Warning: SMT-RAT directory not found.";
        public static final String SMTRAT_GRAPHICS_DIR_EXCEPTION = "Warning: SMT-RAT graphics directory not found.";
        public static final String SMTRAT_SOURCE_DIR_EXCEPTION = "Warning: SMT-RAT source directory not found.";
        public static final String XML_EXCEPTION  = "File does not contain a valid Strategy data structure.";

        public IOToolsException( String s )
        {
            super( s );
        }
    }

    private static class PNGFilter extends FileFilter
    {
        @Override
        public boolean accept( File f )
        {
            return ( f.getName().toLowerCase().endsWith( ".png" ) || f.isDirectory() );
        }

        @Override
        public String getDescription()
        {
            return "PNG (*.png)";
        }
    }

    private static class StrategyHeaderFilter implements FilenameFilter
    {
        @Override
        public boolean accept( File f, String name )
        {
            return ( name.endsWith( ".h" ) && !name.equals( STRATEGIES_HEADER_CLASS + ".h" ) );
        }
    }

    private static class XMLFilter extends FileFilter
    {
        @Override
        public boolean accept( File f )
        {
            return ( f.getName().toLowerCase().endsWith( ".xml" ) || f.isDirectory() );
        }

        @Override
        public String getDescription()
        {
            return "XML (*.xml)";
        }
    }
}
