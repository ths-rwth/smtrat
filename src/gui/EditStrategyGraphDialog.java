import edu.uci.ics.jung.visualization.VisualizationViewer;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import javax.swing.AbstractAction;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.KeyStroke;
import javax.swing.event.CaretEvent;
import javax.swing.event.CaretListener;
import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.Caret;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;
import javax.swing.text.Highlighter.Highlight;
import javax.swing.text.PlainDocument;
import java.io.File;
import java.io.FileReader;
import java.io.BufferedReader;
import java.io.IOException;

/**
 * @file EditStrategyGraphDialog.java
 *
 * @author  Henrik Schmitz
 * @since   2012-10-03
 * @version 2012-11-19
 */
public class EditStrategyGraphDialog extends JDialog
{
    public static final String DELETE_EDGE = "Delete";
    public static final String DELETE_VERTEX = "Delete";
    public static final String ADD_EDGE = "Add Condition";
    public static final String ADD_VERTEX_AND_EDGE = "Add Backend";
    public static final String EDIT_EDGE = "Edit";
    public static final String EDIT_VERTEX = "Edit";
    private static final int DIALOG_PADDING = 500;
    private static final int DIALOG_EDIT_VERTEX_PADDING = 200;
    
    private final GUI gui;
    private final VisualizationViewer visualization;
    private final StrategyGraph graph;
    
    private enum DialogType { AddEdge, AddVertexAndEdge, EditEdge, EditVertex }
    private final DialogType type;
    
    private Edge edge;
    private Condition condition;
    private Vertex vertex;
    private Module module;
    
    private JComboBox<Module> moduleComboBox;
    private JTextArea conditionTextArea;
    private JComboBox<String> propositionComboBox;

    private ConditionCaretListener conditionCaretListener;

    private ConditionPlainDocument conditionPlainDocument;
    
    private boolean dialogShown;

    private DefaultHighlightPainter highlightPainter;

    private EditStrategyGraphDialog( GUI gui, Edge edge, Vertex vertex, DialogType type )
    {
        super( gui, true );
        this.gui = gui;
        visualization = gui.getVisualization();
        graph = (StrategyGraph) visualization.getModel().getGraphLayout().getGraph();
        if( edge!=null )
        {
            this.edge = edge;
        }
        condition = new Condition();
        if( vertex!=null )
        {
            this.vertex = vertex;
            module = vertex.getModule();
        }
        this.type = type;
        dialogShown = false;

        ClosingOkAction closingOkAction = new ClosingOkAction();
        getRootPane().getInputMap( JComponent.WHEN_IN_FOCUSED_WINDOW ).put( KeyStroke.getKeyStroke( KeyEvent.VK_ENTER, 0 ), "Ok" );
        getRootPane().getActionMap().put( "Ok", closingOkAction );
        ClosingCancelAction closingCancelAction = new ClosingCancelAction();
        getRootPane().getInputMap( JComponent.WHEN_IN_FOCUSED_WINDOW ).put( KeyStroke.getKeyStroke( KeyEvent.VK_ESCAPE, 0 ), "Cancel" );
        getRootPane().getActionMap().put( "Cancel", closingCancelAction );
        InstructionsAction instructionsAction = new InstructionsAction();
        getRootPane().getInputMap( JComponent.WHEN_IN_FOCUSED_WINDOW ).put( KeyStroke.getKeyStroke( KeyEvent.VK_F1, 0 ), "Instructions" );
        getRootPane().getActionMap().put( "Instructions", instructionsAction );
        AddPropositionAction addPropositionAction = new AddPropositionAction();
        ModuleInfoAction moduleInfoAction = new ModuleInfoAction();
        
        conditionCaretListener = new ConditionCaretListener();
        ConditionFocusListener conditionFocusListener = new ConditionFocusListener();
        ConditionKeyListener conditionKeyListener = new ConditionKeyListener();
        ConditionMouseListener conditionMouseListener = new ConditionMouseListener();
        conditionPlainDocument = new ConditionPlainDocument();

        GridBagLayout gridBagLayout = new GridBagLayout();
        getContentPane().setLayout( gridBagLayout );
        GridBagConstraints gridBagConstraints = new GridBagConstraints();
        Insets paddingLabelInsets = new Insets( 10, 10, 0, DIALOG_PADDING );
        Insets nonPaddingLabelInsets = new Insets( 10, 10, 0, 10 );
        Insets nonLabelInsets = new Insets( 2, 10, 0, 10 );
        Insets buttonPanelInsets = new Insets( 10, 10, 10, 10);
        gridBagConstraints.gridwidth = GridBagConstraints.REMAINDER;
        gridBagConstraints.fill = GridBagConstraints.HORIZONTAL;

        if( type==DialogType.AddVertexAndEdge || type==DialogType.EditVertex )
        {
            if( IOTools.modules==null )
            {
                JOptionPane.showMessageDialog( gui, "Modules could not be loaded.", "Error", JOptionPane.ERROR_MESSAGE );
                return;
            }
            if ( type==DialogType.AddVertexAndEdge )
            {
                setTitle( ADD_VERTEX_AND_EDGE );
            }
            else
            {
                setTitle( EDIT_VERTEX );
                paddingLabelInsets.set( 10, 10, 0, DIALOG_EDIT_VERTEX_PADDING );
            }
            gridBagConstraints.insets = paddingLabelInsets;
            JLabel moduleLabel = new JLabel( "Choose Module:" );
            gridBagLayout.setConstraints( moduleLabel, gridBagConstraints );
            getContentPane().add( moduleLabel );

            gridBagConstraints.insets = nonLabelInsets;
            JPanel modulePanel = new JPanel();
            modulePanel.setLayout( new BoxLayout( modulePanel, BoxLayout.LINE_AXIS ) );
            moduleComboBox = new JComboBox( IOTools.modules.toArray() );
            if( type==DialogType.EditVertex )
            {
                moduleComboBox.setSelectedItem( module );
            }
            gridBagLayout.setConstraints( moduleComboBox, gridBagConstraints );
            modulePanel.add( moduleComboBox );
            modulePanel.add( Box.createRigidArea( new Dimension( 5, 0 ) ) );
            JButton moduleInfoButton = new JButton( "?" );
            moduleInfoButton.addActionListener( moduleInfoAction );
            moduleInfoButton.setMnemonic( KeyEvent.VK_I );
            modulePanel.add( moduleInfoButton );
            gridBagLayout.setConstraints( modulePanel, gridBagConstraints );
            getContentPane().add( modulePanel );
        }

        if( type==DialogType.AddEdge || type==DialogType.AddVertexAndEdge || type==DialogType.EditEdge )
        {
            if( IOTools.propositions==null )
            {
                JOptionPane.showMessageDialog( gui, "Propositions could not be loaded.", "Error", JOptionPane.ERROR_MESSAGE );
                return;
            }
            if ( type==DialogType.AddEdge )
            {
                setTitle( ADD_EDGE );
            }
            else if ( type==DialogType.EditEdge )
            {
                setTitle( EDIT_EDGE );
            }
            gridBagConstraints.insets = paddingLabelInsets;
            JLabel conditionLabel = new JLabel( "Enter Condition:" );
            gridBagLayout.setConstraints( conditionLabel, gridBagConstraints );
            getContentPane().add( conditionLabel );

            gridBagConstraints.insets = nonLabelInsets;
            conditionTextArea = new JTextArea( 10, 0 );
            conditionTextArea.setFont( new Font( Font.MONOSPACED, Font.PLAIN, 14 ) );
            conditionTextArea.setLineWrap( true );
            conditionTextArea.setWrapStyleWord( true );
            conditionTextArea.addCaretListener( conditionCaretListener );
            conditionTextArea.addFocusListener( conditionFocusListener );
            conditionTextArea.addKeyListener( conditionKeyListener );
            conditionTextArea.addMouseListener( conditionMouseListener );
            conditionTextArea.setDocument( conditionPlainDocument );
            if( edge==null || edge.getCondition().isEmpty() )
            {
                conditionTextArea.insert( Condition.TRUE_CONDITION, 0 );
            }
            else
            {
                conditionTextArea.insert( edge.getCondition().toString(), 0 );
            }
            // TabSize must be set after Document
            conditionTextArea.setTabSize( 2 );
            highlightPainter = new DefaultHighlightPainter( conditionTextArea.getSelectionColor() );
            JScrollPane conditionScrollPane = new JScrollPane( conditionTextArea );
            gridBagLayout.setConstraints( conditionScrollPane, gridBagConstraints );
            getContentPane().add( conditionScrollPane );
            
            gridBagConstraints.insets = nonPaddingLabelInsets;
            JLabel instructionsLabel = new JLabel( "<html><p>Press a, e, i, n,o or x to insert logical operators. Press F1 for further details.</p></html>" );
            gridBagLayout.setConstraints( instructionsLabel, gridBagConstraints );
            getContentPane().add( instructionsLabel );

            gridBagConstraints.insets = nonPaddingLabelInsets;
            JPanel propositionPanel = new JPanel();
            propositionPanel.setLayout( new BoxLayout( propositionPanel, BoxLayout.LINE_AXIS ) );
            propositionComboBox = new JComboBox( IOTools.propositions.toArray() );
            propositionComboBox.removeItem( Condition.TRUE_CONDITION );
            propositionPanel.add( propositionComboBox );
            propositionPanel.add( Box.createRigidArea( new Dimension( 5, 0 ) ) );
            JButton addButton = new JButton( "Add" );
            addButton.addActionListener( addPropositionAction );
            addButton.setMnemonic( KeyEvent.VK_A );
            propositionPanel.add( addButton );
            gridBagLayout.setConstraints( propositionPanel, gridBagConstraints );
            getContentPane().add( propositionPanel );
        }
 
        gridBagConstraints.fill = GridBagConstraints.NONE;
        gridBagConstraints.anchor = GridBagConstraints.CENTER;
        gridBagConstraints.insets = buttonPanelInsets;

        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout( new BoxLayout( buttonPanel, BoxLayout.LINE_AXIS ) );
        JButton okButton = new JButton( "Ok" );
        okButton.addActionListener( closingOkAction );
        okButton.setMnemonic( KeyEvent.VK_O );
        buttonPanel.add( okButton );
		buttonPanel.add( Box.createRigidArea( new Dimension( 5, 0 ) ) );
        JButton cancelButton = new JButton( "Cancel" );
        cancelButton.addActionListener( closingCancelAction );
        cancelButton.setMnemonic( KeyEvent.VK_C );
		buttonPanel.add( cancelButton );
        gridBagLayout.setConstraints( buttonPanel, gridBagConstraints );
        getContentPane().add( buttonPanel );
        
        pack();
        setDefaultCloseOperation( JDialog.DISPOSE_ON_CLOSE );
        setLocationRelativeTo( gui );
        setResizable( false );
        setVisible( true );
    }
    
    public static void showAddEdgeDialog( GUI gui, Edge edge )
    {
        EditStrategyGraphDialog esgd = new EditStrategyGraphDialog( gui, edge, null, EditStrategyGraphDialog.DialogType.AddEdge );
    }

    public static void showAddVertexAndEdgeDialog( GUI gui, Vertex vertex )
    {
        EditStrategyGraphDialog esgd = new EditStrategyGraphDialog( gui, null, vertex, EditStrategyGraphDialog.DialogType.AddVertexAndEdge );
    }

    public static void showEditEdgeDialog( GUI gui, Edge edge )
    {
        EditStrategyGraphDialog esgd = new EditStrategyGraphDialog( gui, edge, null, EditStrategyGraphDialog.DialogType.EditEdge );
    }

    public static void showEditVertexDialog( GUI gui, Vertex vertex )
    {
        EditStrategyGraphDialog esgd = new EditStrategyGraphDialog( gui, null, vertex, EditStrategyGraphDialog.DialogType.EditVertex );
    }
    
    private void setConditionText( String text )
    {
        try
        {
            conditionTextArea.setCaretPosition( 0 );
            int len = conditionTextArea.getText().length();
            if( len>0 )
            {
                ((ConditionPlainDocument) conditionTextArea.getDocument()).remove( 0, len );
            }
            ((ConditionPlainDocument) conditionTextArea.getDocument()).insertString( 0, text, null );
        }
        catch( BadLocationException ex )
        {
            JOptionPane.showMessageDialog( EditStrategyGraphDialog.this, ex.toString(), "Error", JOptionPane.ERROR_MESSAGE );
        }
    }
    
    private class AddPropositionAction extends AbstractAction
    {
        @Override
        public void actionPerformed( ActionEvent ae )
        {
            try
            {
                if( conditionTextArea.getText().equals( Condition.TRUE_CONDITION ) )
                {
                    setConditionText( "" );
                }
                
                Caret c = conditionTextArea.getCaret();

                if( c.getMark()!=c.getDot() )
                {
                    int offs;
                    if( c.getMark()<c.getDot() )
                    {
                        offs = c.getMark();
                    }
                    else
                    {
                        offs = c.getDot();
                    }
                    conditionPlainDocument.remove( offs, conditionTextArea.getSelectedText().length() );
                }

                conditionTextArea.insert( propositionComboBox.getSelectedItem().toString(), c.getDot() );
                conditionTextArea.requestFocus();
            }
            catch( Exception ex )
            {
                JOptionPane.showMessageDialog( EditStrategyGraphDialog.this, ex.toString(), "Error", JOptionPane.ERROR_MESSAGE );
            }
        }
    }

    private class ConditionCaretListener implements CaretListener
    {
        private int oldCaretPosition = 0;
        private Highlight highlight;
        
        @Override
        public void caretUpdate( CaretEvent ce )
        {
            conditionTextArea.getCaret().setSelectionVisible( true );
            if( highlight!=null )
            {
                conditionTextArea.getHighlighter().removeHighlight( highlight );
            }
            
            int markCaretPosition = conditionTextArea.getCaret().getMark();
            int currentCaretPosition = conditionTextArea.getCaret().getDot();
            
            if( currentCaretPosition!=oldCaretPosition )
            {
                int newCaretPositions = condition.calculateTextPosition( oldCaretPosition, currentCaretPosition );
                oldCaretPosition = newCaretPositions;
                if( markCaretPosition!=currentCaretPosition )
                {
                    conditionTextArea.moveCaretPosition( newCaretPositions );
                    try
                    {                    
                        if( markCaretPosition<newCaretPositions )
                        {
                            highlight = (Highlight) conditionTextArea.getHighlighter().addHighlight( markCaretPosition, newCaretPositions, highlightPainter );
                        }
                        else
                        {
                            highlight = (Highlight) conditionTextArea.getHighlighter().addHighlight( newCaretPositions, markCaretPosition, highlightPainter );
                        }
                    }
                    catch( BadLocationException ex )
                    {
                        JOptionPane.showMessageDialog( EditStrategyGraphDialog.this, ex.toString(), "Error", JOptionPane.ERROR_MESSAGE );
                    }
                }
                else
                {
                    conditionTextArea.setCaretPosition( newCaretPositions );
                }
            }
            conditionTextArea.getCaret().setSelectionVisible( false );
        }
    }
    
    private class ConditionFocusListener implements FocusListener
    {
        @Override
        public void focusGained( FocusEvent fe )
        {
            if( conditionTextArea.getText().equals( Condition.TRUE_CONDITION ) )
            {
                setConditionText( "" );
            }
        }

        @Override
        public void focusLost( FocusEvent fe )
        {
            if( conditionTextArea.getText().equals( "" ) && !dialogShown )
            {
                setConditionText( Condition.TRUE_CONDITION );
            }
        }
    }
    
    private class ConditionKeyListener implements KeyListener
    {
        @Override
        public void keyTyped( KeyEvent ke ){}

        @Override
        public void keyPressed( KeyEvent ke )
        {
            if( conditionTextArea.getCaret().getDot()!=conditionTextArea.getCaret().getMark() && !ke.isShiftDown() && ( ke.getKeyCode()==KeyEvent.VK_LEFT || ke.getKeyCode()==KeyEvent.VK_RIGHT || ke.getKeyCode()==KeyEvent.VK_DOWN || ke.getKeyCode()==KeyEvent.VK_UP ) )
            {
                conditionCaretListener.caretUpdate( null );
            }
            else if( ke.getKeyCode()==KeyEvent.VK_SHIFT )
            {
                conditionCaretListener.caretUpdate( null );
                conditionTextArea.getCaret().setSelectionVisible( true );
            }
        }

        @Override
        public void keyReleased( KeyEvent ke ){}
    }
    
    private class ConditionMouseListener implements MouseListener
    {
        @Override
        public void mouseClicked( MouseEvent me ){}
        
        @Override
        public void mouseEntered( MouseEvent me ){}

        @Override
        public void mouseExited( MouseEvent me){}

        @Override
        public void mousePressed( MouseEvent me ) 
        {
            if( me.getModifiersEx()==InputEvent.BUTTON1_DOWN_MASK )
            {
                conditionCaretListener.caretUpdate( null );
                conditionTextArea.getCaret().setSelectionVisible( true );
            }
        }

        @Override
        public void mouseReleased( MouseEvent me )
        {
            if( me.getModifiersEx()==InputEvent.BUTTON1_DOWN_MASK )
            {
                conditionCaretListener.caretUpdate( null );
                conditionTextArea.getCaret().setSelectionVisible( false );
            }
        }
    }
    
    private class ConditionPlainDocument extends PlainDocument
    {
        @Override
        public void insertString( int offs, String text, AttributeSet a ) throws BadLocationException
        {
            String str = condition.addElementAtTextPosition( offs, text );
            if( !str.equals( "" ) )
            {
                super.insertString( offs, str, a );
            }
            else
            {
                if( text.length()>1 )
                {
                    dialogShown = true;
                    JOptionPane.showMessageDialog( EditStrategyGraphDialog.this, "The copied and pasted value does not contain a correct Condition.", "Information", JOptionPane.INFORMATION_MESSAGE );
                    dialogShown = false;
                }
            }
        }

        @Override
        public void remove( int offs, int len ) throws BadLocationException
        {   
            Caret c = conditionTextArea.getCaret();
            if( c.getDot()==c.getMark() )
            {
                int index = condition.calculateIndexPosition( c.getDot() );
                // Equals 'Return' key has been pressed
                if( offs!=c.getDot() )
                {
                    len = condition.getLength( index-1 );
                    offs = offs-(len-1);
                    condition.removeElement( index-1 );
                }
                // Equals 'Del' key has been pressed
                else
                {
                    len = condition.getLength( index );
                    condition.removeElement( index );
                }
            }
            else
            {
                int start, end;
                if( c.getDot()<c.getMark() )
                {
                    start = c.getDot();
                    end = c.getMark();
                }
                else
                {
                    start = c.getMark();
                    end = c.getDot();
                }
                
                int startIndex = condition.calculateIndexPosition( start );
                int endIndex = condition.calculateIndexPosition( end );
                for( int i=startIndex; i<endIndex; i++ )
                {
                    condition.removeElement( startIndex );
                }   
            }
            super.remove( offs, len );
        }
    }

    private class ClosingCancelAction extends AbstractAction
    {
        @Override
        public void actionPerformed( ActionEvent ae )
        {
            try
            {
                if( type==DialogType.AddEdge )
                {
                    graph.removeEdge( edge );
                    visualization.repaint();
                }
                setVisible( false );
                dispose();
            }
            catch( Exception ex )
            {
                JOptionPane.showMessageDialog( EditStrategyGraphDialog.this, ex.toString(), "Error", JOptionPane.ERROR_MESSAGE );
            }
        }
    }

    private class ClosingOkAction extends AbstractAction
    {
        @Override
        public void actionPerformed( ActionEvent ae )
        {
            try
            {
                boolean graphChanged = false;
                if( type!=DialogType.EditVertex )
                {
                    if( !RecursiveDescentParser.parse( condition ) )
                    {
                        conditionTextArea.requestFocus();
                        throw new RecursiveDescentParser.ParserException( RecursiveDescentParser.ParserException.CONDITION_NOT_VALID );
                    }
                    if( type==DialogType.AddEdge || ( type==DialogType.EditEdge && !condition.toString().equals( edge.getCondition().toString() ) ) )
                    {
                        edge.setCondition( condition );
                        graphChanged = true;
                    }
                    else if( type==DialogType.AddVertexAndEdge )
                    {
                        graph.addEdge( new Edge( condition ), vertex, new Vertex( (Module) moduleComboBox.getSelectedItem() ) );
                        graphChanged = true;
                    }
                }
                else
                {
                    if( !module.getName().equals( moduleComboBox.getSelectedItem().toString() ) )
                    {
                        vertex.setModule( (Module) moduleComboBox.getSelectedItem() );
                        graphChanged = true;
                    }
                }

                if( graphChanged )
                {
                    visualization.fireStateChanged();
                    visualization.repaint();
                }
                setVisible( false );
                dispose();
            }
            catch( RecursiveDescentParser.ParserException ex )
            {
                JOptionPane.showMessageDialog( EditStrategyGraphDialog.this, ex.getMessage(), "Information", JOptionPane.INFORMATION_MESSAGE );
            }
            catch( Exception ex )
            {
                JOptionPane.showMessageDialog( EditStrategyGraphDialog.this, ex.toString(), "Error", JOptionPane.ERROR_MESSAGE );
            }
        }
    }
    
    private class InstructionsAction extends AbstractAction
    {
        @Override
        public void actionPerformed( ActionEvent ae )
        {
            try
            {
                gui.openInstructions();
            }
            catch( Exception ex )
            {
                JOptionPane.showMessageDialog( EditStrategyGraphDialog.this, ex.toString(), "Error", JOptionPane.ERROR_MESSAGE );
            }
        }
    }

    private class ModuleInfoAction extends AbstractAction
    {
        @Override
        public void actionPerformed( ActionEvent ae )
        {
            int textAreaWidth = 50;
            int textWidth = (textAreaWidth*3)/2;
            String moduleName = moduleComboBox.getSelectedItem().toString() + new String( "Module" );
            Config config = new Config();
            File file = new File( config.getModulesPath() + File.separator + moduleName + File.separator + moduleName + ".tex" );
            try ( BufferedReader readFile = new BufferedReader( new FileReader( file ) ) )
            {
                String line;
                StringBuilder ret = new StringBuilder();
                while( (line = readFile.readLine())!=null )
                {
                    ret.append( line );
                    ret.append(" ");
                }
                JTextArea textArea = new JTextArea(20, textAreaWidth);
                String infoText = ret.toString().replace( "~", " " );;
                infoText = infoText.replaceAll( "\\$", "" );
                infoText = infoText.replaceAll( "\\.", "\\. " );
                infoText = infoText.replaceAll( "\\,", "\\, " );
                infoText = infoText.replaceAll( "\\;", "\\; " );
                infoText = infoText.replaceAll( "\\:", "\\: " );
                while( !infoText.equals( infoText.replaceAll( "  ", " " ) ) )
                {
                    infoText = infoText.replaceAll( "  ", " " );
                }
                String paragraphString = new String("paragraph");
                StringBuilder sb = new StringBuilder();
                StringBuilder sbForLastWord = new StringBuilder();
                boolean firstWordInLineSet = false;
                int j = 0;
                boolean paragraph = false;
                for( int i = 0; i < infoText.length(); i++ )
                {
                    j++;
                    if( infoText.charAt(i) == ' ' )
                    {
                        if( !paragraph )
                        {
                            paragraph = sbForLastWord.toString().contains( paragraphString );
                            if( paragraph )
                            {
                                j = 0;
                            }
                        }
                        if( paragraph )
                        {
                            if( sbForLastWord.toString().contains( "}" ) )
                            {
                                sb.append("\n\n");
                                sb.append( sbForLastWord.toString() );
                                sbForLastWord.setLength( 0 );
                                sb.append(":\n");
                                j = 0;
                                firstWordInLineSet = false;
                                paragraph = false;
                            }
                            else
                            {
                                sbForLastWord.append(" ");
                            }
                        }
                        else
                        {
                            if( firstWordInLineSet )
                            {
                                sb.append( " " );
                            }
                            else
                            {
                                firstWordInLineSet = true;
                            }
                            sb.append( sbForLastWord.toString() );
                            sbForLastWord.setLength( 0 );
                        }
                    }
                    else
                    {
                        sbForLastWord.append( infoText.charAt(i) );
                    }
                    if( j == textWidth )
                    {
                        j = 0;
                        sb.append("\n");
                        firstWordInLineSet = false;
                    }
                }
                infoText = sb.toString();
                infoText = infoText.replaceAll( "\\\\paragraph\\{(.+?)\\}", "$1" );
                infoText = infoText.replaceAll( "\\{", "" );
                infoText = infoText.replaceAll( "\\}", "" );
                infoText = infoText.replaceAll( "\\\\cite", "" );
                infoText = infoText.replaceAll( "\\\\emph", "" );
                infoText = infoText.replaceAll( "\\\\", "" );
                textArea.setText(infoText);
                textArea.setEditable(false);
                JScrollPane scrollPane = new JScrollPane(textArea);
                String dialogName = new String( "Information to the " ) + moduleName;
                JOptionPane.showMessageDialog(EditStrategyGraphDialog.this, scrollPane, dialogName, JOptionPane.INFORMATION_MESSAGE);
            }
            catch( IOException ex )
            {
                JOptionPane.showMessageDialog( gui, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
            }
        }
    }
}