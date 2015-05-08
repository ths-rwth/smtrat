import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.io.IOException;
import javax.swing.*;

/**
 * @file InstructionsDialog.java
 *
 * @author Henrik Schmitz
 * @since   2013-02-01
 * @version 2013-02-04
 */
public class InstructionsDialog extends JDialog
{
    private static final String HELP_PAGE_FILE = "file://" + System.getProperty( "user.dir" ) + "/help.html";
    
    public InstructionsDialog( GUI gui )
    {
        super( gui, "Instructions", true );
        
        OkAction okAction = new OkAction();
        getRootPane().getInputMap( JComponent.WHEN_IN_FOCUSED_WINDOW ).put( KeyStroke.getKeyStroke( KeyEvent.VK_ESCAPE, 0 ), "Ok" );
        getRootPane().getActionMap().put( "Ok", okAction );
        
        GridBagLayout gridBagLayout = new GridBagLayout();
        getContentPane().setLayout( gridBagLayout );
        GridBagConstraints gridBagConstraints = new GridBagConstraints();
        gridBagConstraints.gridwidth = GridBagConstraints.REMAINDER;
        gridBagConstraints.anchor = GridBagConstraints.CENTER;
        
        gridBagConstraints.insets = new Insets( 10, 10, 0, 10 );
        JEditorPane instructionsEditorPane = new JEditorPane();
        instructionsEditorPane.setEditable( false );
        try
        {
            instructionsEditorPane.setPage( HELP_PAGE_FILE );
        }
        catch( IOException ex )
        {
            JOptionPane.showMessageDialog( gui, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
            return;
        }
        JScrollPane instructionsScrollPane = new JScrollPane( instructionsEditorPane );
        instructionsScrollPane.setVerticalScrollBarPolicy( JScrollPane.VERTICAL_SCROLLBAR_ALWAYS );
        instructionsScrollPane.setHorizontalScrollBarPolicy( JScrollPane.HORIZONTAL_SCROLLBAR_NEVER );
        instructionsScrollPane.setPreferredSize( new Dimension( (GUI.VISUALIZATION_WIDTH-100), (GUI.VISUALIZATION_HEIGHT-100) ) );
        instructionsScrollPane.setMinimumSize( new Dimension( 10, 10 ) );
        gridBagLayout.setConstraints( instructionsScrollPane, gridBagConstraints );
        getContentPane().add( instructionsScrollPane );
        
        gridBagConstraints.insets = new Insets( 10, 10, 10, 10 );
        JButton okButton = new JButton( "Ok" );
        okButton.addActionListener( okAction );
        okButton.setMnemonic( KeyEvent.VK_O );
        gridBagLayout.setConstraints( okButton, gridBagConstraints );
        getContentPane().add( okButton );

        pack();
        setDefaultCloseOperation( JDialog.DISPOSE_ON_CLOSE );
        setLocationRelativeTo( gui );
        setResizable( false );
        setVisible( true );
    }
    
    public static void showDialog( GUI gui )
    {
        InstructionsDialog id = new InstructionsDialog( gui );
    }
    
    private class OkAction extends AbstractAction
    {
        @Override
        public void actionPerformed( ActionEvent ae )
        {
            setVisible( false );
            dispose();
        }
    }
}