import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import javax.swing.*;

/**
 * Dialog showing the GPL warranty and conditions.
 *
 * @author Henrik Schmitz
 * @author Ulrich Loup
 * @since   2012-02-27
 * @version 2012-11-17
 */
public class LicenseDialog extends JDialog
{
    private static final String nl = System.lineSeparator();
    private static final String LICENSE = "Copyright (c)  2015  Florian Corzilius <corzilius@cs.rwth-aachen.de>,\n                     Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>,\n                     Sebastian Junges <sebastian.junges@cs.rwth-aachen.de>,\n                     Stefan Schupp <stefan.schupp@cs.rwth-aachen.de>,\n                     Erika Abraham <abraham@cs.rwth-aachen.de>\n\nPermission is hereby granted, free of charge, to any person obtaining a copy\nof this software and associated documentation files (the \"Software\"), to deal\nin the Software without restriction, including without limitation the rights\nto use, copy, modify, merge, publish, distribute, sublicense, and/or sell\ncopies of the Software, and to permit persons to whom the Software is\nfurnished to do so, subject to the following conditions:\n\nThe above copyright notice and this permission notice shall be included in\nall copies or substantial portions of the Software.\n\nTHE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR\nIMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,\nFITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE\nAUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER\nLIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,\nOUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN\nTHE SOFTWARE.";

    /**
     * Show the license frame.
     */
    public LicenseDialog( GUI gui )
    {
        super( gui, "License", true );
        
        OkAction okAction = new OkAction();
        getRootPane().getInputMap( JComponent.WHEN_IN_FOCUSED_WINDOW ).put( KeyStroke.getKeyStroke( KeyEvent.VK_ENTER, 0 ), "Ok" );
        getRootPane().getInputMap( JComponent.WHEN_IN_FOCUSED_WINDOW ).put( KeyStroke.getKeyStroke( KeyEvent.VK_ESCAPE, 0 ), "Ok" );
        getRootPane().getActionMap().put( "Ok", okAction );
        
        GridBagLayout gridBagLayout = new GridBagLayout();
        getContentPane().setLayout( gridBagLayout );
        GridBagConstraints gridBagConstraints = new GridBagConstraints();
        gridBagConstraints.gridwidth = GridBagConstraints.REMAINDER;
        gridBagConstraints.anchor = GridBagConstraints.CENTER;
        
        gridBagConstraints.insets = new Insets( 10, 10, 0, 10 );
        JTextArea licenseTextArea = new JTextArea( LICENSE, 20, 0 );
        licenseTextArea.setEditable( false );
        licenseTextArea.setFont( new Font( Font.MONOSPACED, Font.PLAIN, 14 ) );
        licenseTextArea.setLineWrap( false );
        JScrollPane licenseScrollPane = new JScrollPane( licenseTextArea );
        gridBagLayout.setConstraints( licenseScrollPane, gridBagConstraints );
        getContentPane().add( licenseScrollPane );
        
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
        LicenseDialog ld = new LicenseDialog( gui );
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