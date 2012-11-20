/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT. If not, see <http://www.gnu.org/licenses/>.
 *
 */

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
// Enter full path
//       - needs SMT-RAT source code
 *
 * @author  Henrik Schmitz
 * @author  Ulrich Loup
 * @since   2012-02-07
 * @version 2012-11-18
 */
public class IOTools
{
// Path to be changed
    private static final File SMTRAT_BASE_DIR = new File( ".." + File.separator + ".." + File.separator + ".." + File.separator );
    public static final File SMTRAT_GRAPHICS_DIR = new File( SMTRAT_BASE_DIR + File.separator + "htdocs" + File.separator + "images" );
    private static final File SMTRAT_SOURCE_DIR = new File( SMTRAT_BASE_DIR + File.separator + "src" + File.separator + "lib" );
    private static final File MODULES_SOURCE_DIR = new File( SMTRAT_SOURCE_DIR + File.separator + "modules" );

    private static final File MODULE_TYPE_SOURCE_FILE = new File( SMTRAT_SOURCE_DIR + File.separator + "ModuleType.h" );
    private static final File PROPOSITION_SOURCE_FILE = new File( SMTRAT_SOURCE_DIR + File.separator + "Condition.h" );

// Path to be changed
    private static final File SMTRAT_BUILDFILE = new File( SMTRAT_SOURCE_DIR + File.separator + "CMakeLists.txt" );
    
    private static final String CONDITION_CLASS = "Condition";
    private static final String MODULE_TYPE = "ModuleType";
    private static final String MANAGER_CLASS = "Manager";
    
    public static final ArrayList<Module> modules = readModules();
    public static final ArrayList<String> propositions = readPropositions();
    public static final ArrayList<String> notAllowedSolverNames = new ArrayList<>();
    public static final ArrayList<String> existingSolverNames = readExistingSolverNames();
    
    private static GUI gui;
    private static FRLayout layout;
    
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
        if( !MODULES_SOURCE_DIR.exists() )
        {
            throw new IOToolsException( IOToolsException.MODULES_SOURCE_DIR_EXCEPTION );
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
    
    public static String openGraph()
    {
        try
        {
            JFileChooser fileChooser = new JFileChooser();
            fileChooser.setDialogTitle( "Open" );
            fileChooser.removeChoosableFileFilter( fileChooser.getChoosableFileFilters()[0] );
            fileChooser.setFileFilter( new XMLFilter() );
            fileChooser.setMultiSelectionEnabled( false );
            while( true )
            {
                int option = fileChooser.showOpenDialog( gui );
                if( option==JFileChooser.APPROVE_OPTION )
                {
                    String graphFilePath = fileChooser.getSelectedFile().getPath();
                    if( !graphFilePath.toLowerCase().endsWith( ".xml" ) )
                    {
                        graphFilePath += ".xml";
                        fileChooser.setSelectedFile( new File( graphFilePath ) );
                    }
                    if( !fileChooser.getSelectedFile().canRead() )
                    {
                        JOptionPane.showMessageDialog( gui, "Permission denied. Please select a different file.", "Information", JOptionPane.INFORMATION_MESSAGE );
                        continue;
                    }
                    else
                    {
                        createGraph( graphFilePath );
                        return graphFilePath;
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
    
    public static String saveGraph( String graphFilePath, boolean saveAs )
    {
        try
        {
            if( graphFilePath==null || saveAs )
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
                while( true )
                {
                    int option = fileChooser.showSaveDialog( gui );
                    if( option==JFileChooser.APPROVE_OPTION )
                    {
                        graphFilePath = fileChooser.getSelectedFile().getPath();
                        if( !graphFilePath.toLowerCase().endsWith(".xml") )
                        {
                            graphFilePath += ".xml";
                            fileChooser.setSelectedFile( new File( graphFilePath ) );
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
            createXML( graphFilePath );
            return graphFilePath;
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
    
    private static void createGraph( String graphFilePath ) throws IOException, ParserConfigurationException, SAXException, IOToolsException
    {
        StrategyGraph graph = new StrategyGraph();
        HashMap<Integer,Vertex> vertices = new HashMap();

        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = dbf.newDocumentBuilder();
        Document document = db.parse( graphFilePath );

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
            
            Element typeElement = (Element) moduleElement.getLastChild();
            if( !typeElement.getTagName().equals( "type" ) )
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
            String type = ((Text) typeElement.getFirstChild()).getData();
            Vertex vertex;
            if( name.equals( StrategyGraph.ROOT_VERTEX_MODULE_NAME ) )
            {
                vertex = graph.getRoot();
            }
            else
            {
                vertex = new Vertex( new Module( name, type ) );
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
    
    private static void createXML( String graphFilePath ) throws TransformerConfigurationException, TransformerException, ParserConfigurationException
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
            
            Element typeElement = document.createElement( "type" );
            typeElement.appendChild( document.createTextNode( v.getModule().getType() ) );
            moduleElement.appendChild( typeElement );
        }

        Collection<Edge> edges = graph.getEdges();
        if( !edges.isEmpty() )
        {
            Element edgesElement = document.createElement( "edges" );
            rootElement.appendChild( edgesElement );

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
        StreamResult result = new StreamResult( new File( graphFilePath ) );
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
            if( solverName==null || solverName.equals( "" ) )
            {
                return null;
            }
            
            String tab = "    ";
            String nl = System.lineSeparator();
            String solverNameLowerCase = solverName.toLowerCase();
            String solverNameUpperCase = solverName.toUpperCase();
            
            File headerFile = new File( SMTRAT_SOURCE_DIR.getPath() + File.separator + solverName + ".h" );
            File headerTempFile = null;
            File implementationFile = new File( SMTRAT_SOURCE_DIR.getPath() + File.separator + solverName + ".cpp" );
            File implementationTempFile = null;
            File smtratBuildTempFile = new File( SMTRAT_BUILDFILE.getPath() + "~" );

            if( add )
            {
                StrategyGraph graph = (StrategyGraph) layout.getGraph();
                HashMap<Integer,Edge> edges = new HashMap<>();
                for( Edge e : (Collection<Edge>) graph.getEdges() )
                {
                    edges.put( e.getPriority(), e );
                }

                String license = "/*" + nl + " * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox" + nl + " * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges" + nl + " *" + nl + " * This file is part of SMT-RAT." + nl + " *" + nl + " * SMT-RAT is free software: you can redistribute it and/or modify" + nl + " * it under the terms of the GNU General Public License as published by" + nl + " * the Free Software Foundation, either version 3 of the License, or"+ nl + " * (at your option) any later version." + nl + " *" + nl + " * SMT-RAT is distributed in the hope that it will be useful," + nl + " * but WITHOUT ANY WARRANTY; without even the implied warranty of" + nl + " * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the" + nl + " * GNU General Public License for more details." + nl + " *" + nl + " * You should have received a copy of the GNU General Public License" + nl + " * along with SMT-RAT. If not, see <http://www.gnu.org/licenses/>." + nl + " *" + nl + " */" + nl + nl;

                String headerString = license + "/**" + nl + " * @file " + solverName + ".h" + nl + " *" + nl + " */" + nl + "#ifndef SMTRAT_" + solverNameUpperCase + "_H" + nl + "#define SMTRAT_" + solverNameUpperCase + "_H" + nl + nl + "#include \"Manager.h\"" + nl + nl + "namespace smtrat" + nl + "{" + nl + tab + "class " + solverName + ":" + nl + tab + tab + "public Manager" + nl + tab + "{" + nl + tab + tab + "public:" + nl + tab + tab + tab + solverName + "( Formula* = new Formula( AND ) );" + nl + tab + tab + tab + "~" + solverName + "();" + nl + tab + "};" + nl + "}" + tab + "// namespace smtrat" + nl + "#endif" + tab + "/** SMTRAT_" + solverNameUpperCase + "_H */" + nl;

                StringBuilder conditionsString = new StringBuilder();
                StringBuilder graphString = new StringBuilder();

                StringBuilder implementationString = new StringBuilder();
                implementationString.append( license ).append( "/**" ).append( nl ).append( " * @file " ).append( solverName ).append( ".cpp" ).append( nl ).append( " *" ).append( nl ).append( " */" ).append( nl ).append( "#include \"" ).append( solverName ).append( ".h\"" ).append( nl ).append( nl ).append( "namespace smtrat" ).append( nl ).append( "{" ).append( nl );

                for( int i=0; i<edges.size(); i++ )
                {
                    Edge edge = edges.get( i );
                    Edge predecessorEdge = graph.getPredecesssorEdge( edge );
                    Condition condition = edge.getCondition();
                    Vertex successorVertex = (Vertex) graph.getEndpoints( edge ).getSecond();

                    if( !condition.isTrueCondition() )
                    {
                        implementationString.append( tab ).append( "static Condition condition" ).append( i ).append( " = (" ).append( condition.toStringCPP() ).append( ");" ).append( nl );
                        conditionsString.append( nl ).append( tab ).append( "static bool conditionEvaluation" ).append( i ).append( "( Condition _condition )" ).append( nl ).append( tab ).append( "{" ).append( nl ).append( tab ).append( tab ).append( "return condition" ).append( i ).append( " <= _condition;" ).append( nl ).append( tab ).append( "}" ).append( nl );
                    }

                    if( edge.isBackLink() )
                    {
                        graphString.append( tab ).append( tab ).append( "rStrategyGraph().addCondition( " );

                    }
                    else
                    {
                        graphString.append( tab ).append( tab ).append( "rStrategyGraph().addModuleType( " );
                    }

                    if( predecessorEdge==null )
                    {
                        graphString.append( "0" ).append( ", " );
                    }
                    else
                    {
                        graphString.append( predecessorEdge.getPriority()+1 ).append( ", " );
                    }

                    if( edge.isBackLink() )
                    {
                        predecessorEdge = graph.getPredecesssorEdge( successorVertex );
                        graphString.append( predecessorEdge.getPriority()+1 );
                    }
                    else
                    {
                        graphString.append( successorVertex.getModule().getType() );
                    }

                    if( condition.isTrueCondition() )
                    {
                        graphString.append( ", isCondition );" ).append( nl );
                    }
                    else
                    {
                        graphString.append( ", conditionEvaluation" ).append( i ).append( " );" ).append( nl );
                    }
                }
                implementationString.append( conditionsString );
                implementationString.append( nl ).append( tab ).append( solverName ).append( "::" ).append( solverName ).append( "( Formula* _inputFormula ) " ).append( nl ).append( tab ).append( tab ).append( "Manager( _inputFormula )" ).append( nl ).append( tab ).append( "{" ).append( nl );
                implementationString.append( graphString );
                implementationString.append( tab ).append( "}" ).append( nl ).append( nl ).append( tab ).append( solverName ).append( "::~" ).append( solverName ).append( "(){}" ).append( nl ).append( nl ).append( "}" ).append( tab ).append( "// namespace smtrat" );
                
                if( headerFile.exists() )
                {
                    headerTempFile = new File( headerFile.getPath() + "~" );
                    Files.copy( headerFile.toPath(), headerTempFile.toPath(), StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.COPY_ATTRIBUTES );
                }
                try( PrintWriter writeFile = new PrintWriter( new FileWriter( headerFile ) ) )
                {
                    writeFile.print( headerString );
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
                
                if( implementationFile.exists() )
                {
                    implementationTempFile = new File( implementationFile.getPath() + "~" );
                    Files.copy( implementationFile.toPath(), implementationTempFile.toPath(), StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.COPY_ATTRIBUTES );
                }
                try( PrintWriter writeFile = new PrintWriter( new FileWriter( implementationFile ) ) )
                {
                    writeFile.print( implementationString.toString() );
                    writeFile.flush();
                }
                catch( Exception ex )
                {
                    if( headerTempFile!=null && headerTempFile.exists() )
                    {
                        Files.copy( headerTempFile.toPath(), headerFile.toPath(), StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.COPY_ATTRIBUTES );
                        Files.delete( headerTempFile.toPath() );
                    }
                    if( implementationTempFile!=null && implementationTempFile.exists() )
                    {
                        Files.copy( implementationTempFile.toPath(), implementationFile.toPath(), StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.COPY_ATTRIBUTES );
                        Files.delete( implementationTempFile.toPath() );
                    }
                    throw ex;
                }
            }

            String newFileContents;
            StringBuilder fileContents = new StringBuilder();
            try ( BufferedReader readFile = new BufferedReader( new FileReader( SMTRAT_BUILDFILE ) ) )
            {
                String line;
                while( (line = readFile.readLine())!=null )
                {
                    fileContents.append( line ).append( nl );
                }

                newFileContents = fileContents.toString().replaceAll( "\\s*set\\(\\s*lib_" + solverNameLowerCase + "_headers\\s*" + solverName + "\\.h\\s*\\)\\s*", nl );
                newFileContents = newFileContents.replaceAll( "\\s*set\\(\\s*lib_" + solverNameLowerCase + "_src\\s*" + solverName + "\\.cpp\\s*\\)\\s*", nl );
                newFileContents = newFileContents.replaceAll( "\\s*install\\(\\s*FILES\\s*\\$\\{lib_" + solverNameLowerCase + "_headers\\}\\s*DESTINATION\\s*include/\\$\\{PROJECT_NAME\\}\\s*\\)\\s*", nl );
                newFileContents = newFileContents.replaceAll( "\\s*\\$\\{lib_" + solverNameLowerCase + "_headers\\}\\s*", nl + tab );
                newFileContents = newFileContents.replaceAll( "\\s*\\$\\{lib_" + solverNameLowerCase + "_src\\}\\s*", nl + tab );
            }

            if( add )
            {
                Pattern definitionStart = Pattern.compile( "\\s*set\\(lib_\\$\\{PROJECT_NAME\\}_SRCS\\s*", Pattern.COMMENTS + Pattern.DOTALL );
                Matcher definitionStartMatcher = definitionStart.matcher( newFileContents );
                if( definitionStartMatcher.find() )
                {
                    int matchIndexStart = definitionStartMatcher.start();
                    int matchIndexEnd = definitionStartMatcher.end();
                    newFileContents = newFileContents.substring( 0, matchIndexStart ) + nl + "set( lib_" + solverNameLowerCase + "_headers " + solverName + ".h )" + nl + "set( lib_" + solverNameLowerCase + "_src " + solverName + ".cpp )" + newFileContents.substring( matchIndexStart, matchIndexEnd ) + "${lib_" + solverNameLowerCase + "_headers} " + nl + tab + "${lib_" + solverNameLowerCase + "_src}" + nl + tab + newFileContents.substring( matchIndexEnd );

                    definitionStart = Pattern.compile( "\\s*install\\(\\s*FILES\\s*", Pattern.COMMENTS + Pattern.DOTALL );
                    definitionStartMatcher = definitionStart.matcher( newFileContents );

                    if( definitionStartMatcher.find() )
                    {
                        matchIndexStart = definitionStartMatcher.start();
                        newFileContents = newFileContents.substring( 0, matchIndexStart ) + nl + "install( FILES ${lib_" + solverNameLowerCase + "_headers} DESTINATION include/${PROJECT_NAME}/lib )" + newFileContents.substring( matchIndexStart );
                    }
                    else
                    {
                        throw new IOToolsException( IOToolsException.ENTRY_POINT_NOT_FOUND );
                    }
                }
                else
                {
                    throw new IOToolsException( IOToolsException.ENTRY_POINT_NOT_FOUND );
                }
            }

            Files.copy( SMTRAT_BUILDFILE.toPath(), smtratBuildTempFile.toPath(), StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.COPY_ATTRIBUTES );

            try( PrintWriter writeFile = new PrintWriter( new FileWriter( SMTRAT_BUILDFILE ) ) )
            {
                writeFile.print( newFileContents );
                writeFile.flush();
                if( !add )
                {
                    if( headerFile.exists() )
                    {
                        Files.delete( headerFile.toPath() );
                    }
                    if( implementationFile.exists() )
                    {
                        Files.delete( implementationFile.toPath() );
                    }
                }
            }
            catch( Exception ex )
            {
                if( headerTempFile!=null && headerTempFile.exists() )
                {
                    Files.copy( headerTempFile.toPath(), headerFile.toPath(), StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.COPY_ATTRIBUTES );
                    Files.delete( headerTempFile.toPath() );
                }
                if( implementationTempFile!=null && implementationTempFile.exists() )
                {
                    Files.copy( implementationTempFile.toPath(), implementationFile.toPath(), StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.COPY_ATTRIBUTES );
                    Files.delete( implementationTempFile.toPath() );
                }
                if( smtratBuildTempFile.exists() )
                {
                    Files.copy( smtratBuildTempFile.toPath(), SMTRAT_BUILDFILE.toPath(), StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.COPY_ATTRIBUTES );
                    Files.delete( smtratBuildTempFile.toPath() );
                }
                throw ex;
            }

            if( headerTempFile!=null && headerTempFile.exists() )
            {
                Files.delete( headerTempFile.toPath() );
            }
            if( implementationTempFile!=null && implementationTempFile.exists() )
            {
                Files.delete( implementationTempFile.toPath() );
            }
            if( smtratBuildTempFile.exists() )
            {
                Files.delete( smtratBuildTempFile.toPath() );
            }
            
            return solverName;
        }
        catch( IOException | IOToolsException ex )
        {
            JOptionPane.showMessageDialog( gui, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
            return null;
        }
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
        String fileContent = removeComments( MODULE_TYPE_SOURCE_FILE );

        int offset = fileContent.split( "enum\\s*" + MODULE_TYPE + "(\\s+|\\{)", 2 )[0].length();
        if( fileContent.length()==offset || !fileContent.contains( "{" ) || !fileContent.contains( "}" ) )
        {
            return null;
        }

        fileContent = fileContent.substring( offset );
        fileContent = fileContent.substring( fileContent.indexOf( "{" )+1, fileContent.indexOf( "}" ) );
        fileContent = fileContent.replaceAll( "\\s", "" );
        String[] moduleTypes = fileContent.split( "," );
        if( moduleTypes.length==0 )
        {
            return null;
        }
        
        for( File f : MODULES_SOURCE_DIR.listFiles( new HeaderFilter() ) )
        {
            String name = f.getName().substring( 0, f.getName().length()-2 );
            // if yes, see if a cpp file or tpp file is existing and check it for the proper getType
            f = new File( MODULES_SOURCE_DIR + File.separator + name + ".cpp" );
            if( !f.exists() )
            {
                f = new File( MODULES_SOURCE_DIR + File.separator + name + ".tpp" );
                if( !f.exists() )
                {
                    continue;
                }
            }

            // search correct module getType (first match)
            int i;
            for( i=0; i<moduleTypes.length; i++ )
            {
                if( moduleTypes[i].contains( name ) )
                {
                    moduleList.add( new Module( name, moduleTypes[i] ) );
                    break;
                }
            }
            // if not found, take name as getType
            if( i==moduleTypes.length )
            {
                moduleList.add( new Module( name ) );
            }
        }

        if( moduleList.isEmpty() )
        {
            return null;
        }
        else
        {
            Collections.sort( moduleList );
            return moduleList;
        }
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

        Pattern managerClassExtension = Pattern.compile( ".*public\\s*" + MANAGER_CLASS + ".*", Pattern.COMMENTS + Pattern.DOTALL );
        for( File f : SMTRAT_SOURCE_DIR.listFiles( new HeaderFilter() ) )
        {
            String name = f.getName();
            name = name.substring( 0, name.length()-2 );
            if( managerClassExtension.matcher( removeComments( f ) ).matches() )
            {
                solverNamesList.add( name );
            }
            else
            {
                notAllowedSolverNames.add( name );
            }
        }
        for( File f : SMTRAT_SOURCE_DIR.listFiles( new ImplementationFilter() ) )
        {
            String name = f.getName();
            name = name.substring( 0, name.length()-4 );
            File header = new File( SMTRAT_SOURCE_DIR + File.separator + name + ".h" );
            if( header.exists() )
            {
                continue;
            }
            else
            {
                notAllowedSolverNames.add( name );
            }
        }
        Collections.sort( solverNamesList );
        return solverNamesList;
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
        
        public static final String ENTRY_POINT_NOT_FOUND = "Warning: Could not find entry point in build file " + SMTRAT_BUILDFILE + ".";
        public static final String MODULES_PARSE_EXCEPTION = "Warning: Could not parse Modules from source files.";
        public static final String MODULES_SOURCE_DIR_EXCEPTION = MODULES_PARSE_EXCEPTION + " Source directory not found.";
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
    
    private static class HeaderFilter implements FilenameFilter
    {
        @Override
        public boolean accept( File f, String name )
        {
            return ( name.endsWith( ".h" ) );
        }
    }
    
    private static class ImplementationFilter implements FilenameFilter
    {
        @Override
        public boolean accept( File f, String name )
        {
            return ( name.endsWith( ".cpp" ) );
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