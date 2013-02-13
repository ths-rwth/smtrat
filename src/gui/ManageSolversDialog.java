/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2013 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges, Henrik Schmitz
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

import java.awt.Color;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.util.ArrayList;
import java.util.Collections;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.swing.AbstractAction;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.KeyStroke;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

/**
 * @file ManageSolversDialog.java
 *
 * @author  Henrik Schmitz
 * @since   2012-11-12
 * @version 2013-02-02
 */
public class ManageSolversDialog extends JDialog
{
    private static final int DIALOG_PADDING = 250;
    private static final int LIST_HEIGHT = 98;
    
    private static ArrayList<String> existingSolverNames;
    private static String notAllowedSolverName;
    private static boolean existingSolverNameEntered;
    private static String solverName;
    
    private static JTextField solverNameTextField;
    private static JButton exportButton;
    private static JScrollPane availableSolversScrollPane;
    
    public ManageSolversDialog( GUI gui, String solverNameSuggestion )
    {
        super( gui, "Manage Solvers", true );
        notAllowedSolverName = IOTools.STRATEGIES_CLASS;
        existingSolverNames = IOTools.existingSolverNames;

        ExportSolverAction exportSolverAction = new ExportSolverAction();
        OkAction okAction = new OkAction();
        getRootPane().getInputMap( JComponent.WHEN_IN_FOCUSED_WINDOW ).put( KeyStroke.getKeyStroke( KeyEvent.VK_ENTER, 0 ), "Ok" );
        getRootPane().getInputMap( JComponent.WHEN_IN_FOCUSED_WINDOW ).put( KeyStroke.getKeyStroke( KeyEvent.VK_ESCAPE, 0 ), "Ok" );
        getRootPane().getActionMap().put( "Ok", okAction );
        SolverNameDocumentListener solverNameDocumentListener = new SolverNameDocumentListener();
        
        GridBagLayout gridBagLayout = new GridBagLayout();
        getContentPane().setLayout( gridBagLayout );
        GridBagConstraints gridBagConstraints = new GridBagConstraints();
        gridBagConstraints.gridwidth = GridBagConstraints.REMAINDER;
        gridBagConstraints.fill = GridBagConstraints.HORIZONTAL;
        
        gridBagConstraints.insets = new Insets( 10, 10, 0, DIALOG_PADDING );
        JLabel solverNameLabel = new JLabel( "Enter Solver name:" );
        gridBagLayout.setConstraints( solverNameLabel, gridBagConstraints );
        getContentPane().add( solverNameLabel );
        gridBagConstraints.insets = new Insets( 2, 10, 0, 10 );
        JPanel solverNamePanel = new JPanel();
        solverNamePanel.setLayout( new BoxLayout( solverNamePanel, BoxLayout.LINE_AXIS ) );
        solverNameTextField = new JTextField( solverNameSuggestion );
        solverNameTextField.getDocument().addDocumentListener( solverNameDocumentListener );
        solverNamePanel.add( solverNameTextField );
		solverNamePanel.add( Box.createRigidArea( new Dimension( 5, 0 ) ) );
        exportButton = new JButton( "Export" );
        exportButton.addActionListener( exportSolverAction );
        exportButton.setMnemonic( KeyEvent.VK_E );
        solverNamePanel.add( exportButton );
        gridBagLayout.setConstraints( solverNamePanel, gridBagConstraints );
        getContentPane().add( solverNamePanel );
        
        gridBagConstraints.insets = new Insets( 10, 10, 0, 10 );
        JLabel availableSolversLabel = new JLabel( "Available Solvers:" );
        gridBagLayout.setConstraints( availableSolversLabel, gridBagConstraints );
        getContentPane().add( availableSolversLabel );
        
        gridBagConstraints.insets = new Insets( 2, 10, 0, 10 );
        availableSolversScrollPane = new JScrollPane();
        Dimension dim = new Dimension( 0, LIST_HEIGHT );
        availableSolversScrollPane.setPreferredSize( dim );
		availableSolversScrollPane.setMaximumSize( dim );
		availableSolversScrollPane.setMinimumSize( dim );
        gridBagLayout.setConstraints( availableSolversScrollPane, gridBagConstraints );
        getContentPane().add( availableSolversScrollPane );

        gridBagConstraints.fill = GridBagConstraints.NONE;
        gridBagConstraints.anchor = GridBagConstraints.CENTER;
        gridBagConstraints.insets = new Insets( 10, 10, 10, 10);
        JButton okButton = new JButton( "Ok" );
        okButton.addActionListener( okAction );
        okButton.setMnemonic( KeyEvent.VK_O );
        gridBagLayout.setConstraints( okButton, gridBagConstraints );
        getContentPane().add( okButton );
        
        checkSolverName();
        updateAvailableSolvers( null, true );

        pack();
        setDefaultCloseOperation( JDialog.DISPOSE_ON_CLOSE );
        setLocationRelativeTo( gui );
        setResizable( false );
        setVisible( true );
    }
    
    public static String showDialog( GUI gui, String solverNameSuggestion)
    {
        ManageSolversDialog msd = new ManageSolversDialog( gui, solverNameSuggestion );
        return solverName;
    }
    
    private void checkSolverName()
    {
        String textInput = solverNameTextField.getText();
        Pattern cppIdentifier = Pattern.compile( "(_|[a-zA-Z])(_|[a-zA-Z]|\\d)*" );
        Matcher cppIdentifierMatcher = cppIdentifier.matcher( textInput );

        if( !cppIdentifierMatcher.matches() || notAllowedSolverName.toLowerCase().equals( textInput.toLowerCase() ) )
        {
            solverNameTextField.setForeground( Color.RED );
            existingSolverNameEntered = false;
            exportButton.setEnabled( false );
        }
        else if( findCorrespondingSolverName( existingSolverNames, textInput )!=null )
        {
            solverNameTextField.setForeground( Color.ORANGE );
            existingSolverNameEntered = true;
            exportButton.setEnabled( true );
        }
        else
        {
            solverNameTextField.setForeground( Color.BLACK );
            existingSolverNameEntered = false;
            exportButton.setEnabled( true );
        }
    }
    
    private String findCorrespondingSolverName( ArrayList<String> list, String value )
    {
        value = value.toLowerCase();
        for( int i=0; i<list.size(); i++ )
        {
            String ret = list.get( i );
            if( ret.toLowerCase().equals( value ) )
            {
                return ret;
            }
        }
        return null;
    }
    
    private void updateAvailableSolvers( String solverName, boolean add )
    {
        if( solverName!=null )
        {
            if( add )
            {
                if( !existingSolverNames.contains( solverName ) )
                {
                    existingSolverNames.add( solverName );
                    Collections.sort( existingSolverNames );
                }
            }
            else
            {
                existingSolverNames.remove( solverName );
            }
        }
        JPanel outerPanel = new JPanel();
        outerPanel.setBackground( Color.WHITE );
        outerPanel.setLayout( new FlowLayout( FlowLayout.LEFT ) );
        
        JPanel availableSolversPanel = new JPanel();
        availableSolversPanel.setBackground( Color.WHITE );
        
        String takeOverText = "Take over this Solver name for export to overwrite existing Solver.";
        String deleteText = "Delete this Solver.";
        
        GridBagLayout gbl = new GridBagLayout();
        availableSolversPanel.setLayout( gbl );
        GridBagConstraints gbc = new GridBagConstraints();
        
        Insets nonPaddingButtonInsets = new Insets( 5, 0, 0, 0 );
        Insets paddingButtonInsets = new Insets( 5, 5, 0, 0 );
        Insets labelInsets = new Insets( 5, 10, 0, 0 );
        
        gbc.anchor = GridBagConstraints.WEST;
        for( int i=0; i<existingSolverNames.size(); i++ )
        {
            String name = existingSolverNames.get( i );
            if( i>0 )
            {
                gbc.insets = nonPaddingButtonInsets;
                
            }
            gbc.weightx = 0.0d;
            gbc.fill = GridBagConstraints.NONE;
            gbc.gridwidth = 1;
            JButton takeOverSolverNameButton = new JButton( "\u2191" );
            takeOverSolverNameButton.addActionListener( new TakeOverSolverNameAction( name ) );
            takeOverSolverNameButton.setBackground( Color.WHITE );
            takeOverSolverNameButton.setToolTipText( takeOverText );
            gbl.setConstraints( takeOverSolverNameButton, gbc );
            availableSolversPanel.add( takeOverSolverNameButton );
            if( i>0 )
            {
                gbc.insets = paddingButtonInsets;
            }
            else
            {
                gbc.insets = new Insets( 0, 5, 0, 0 );
            }
            JButton deleteSolverButton = new JButton( "-" );
            deleteSolverButton.addActionListener( new DeleteSolverAction( name ) );
            deleteSolverButton.setBackground( Color.WHITE );
            deleteSolverButton.setToolTipText( deleteText );
            gbl.setConstraints( deleteSolverButton, gbc );
            availableSolversPanel.add( deleteSolverButton );
            if( i>0 )
            {
                gbc.insets = labelInsets;
            }
            else
            {
                gbc.insets = new Insets( 0, 10, 0, 0 );
            }
            gbc.weightx = 1.0d;
            gbc.fill = GridBagConstraints.HORIZONTAL;
            gbc.gridwidth = GridBagConstraints.REMAINDER;
            JLabel solverLabel = new JLabel( name );
            gbl.setConstraints( solverLabel, gbc );
            availableSolversPanel.add( solverLabel );
        }
        outerPanel.add( availableSolversPanel );
        availableSolversScrollPane.setViewportView( outerPanel );
    }
    
    private class DeleteSolverAction extends AbstractAction
    {
        private final String solverName;
        
        private DeleteSolverAction( String solverName )
        {
            this.solverName = solverName;
        }
        
        @Override
        public void actionPerformed( ActionEvent ae )
        {
            // Escape = -1, Yes = 0, No = 1, Cancel = 2
            int choice = JOptionPane.showConfirmDialog( ManageSolversDialog.this, "Really delete Solver named '" + solverName + "'?", "Question", JOptionPane.YES_NO_OPTION );
            if( choice==-1 || choice==1 )
            {
                return;
            }
            if( IOTools.deleteSolver( solverName )!=null )
            {
                updateAvailableSolvers( solverName, false );
                JOptionPane.showMessageDialog( ManageSolversDialog.this, "Solver deleted successfully.", "Information", JOptionPane.INFORMATION_MESSAGE );
            }
        }
    }

    private class ExportSolverAction extends AbstractAction
    {
        @Override
        public void actionPerformed( ActionEvent ae )
        {
            String textInput = solverNameTextField.getText();
            if( existingSolverNameEntered )
            {
                textInput = findCorrespondingSolverName( existingSolverNames, textInput );
                // Escape = -1, Yes = 0, No = 1, Cancel = 2
                int choice = JOptionPane.showConfirmDialog( ManageSolversDialog.this, "A Solver named '" + textInput + "' already exists. Overwrite this Solver?", "Question", JOptionPane.YES_NO_OPTION );
                if( choice==-1 || choice==1 )
                {
                    return;
                }
            }
            if( (solverName = IOTools.exportSolver( textInput ))!=null )
            {
                updateAvailableSolvers( textInput, true );
                solverNameTextField.setText( "" );
                solverNameTextField.requestFocus();
                JOptionPane.showMessageDialog( ManageSolversDialog.this, "Solver exported successfully.", "Information", JOptionPane.INFORMATION_MESSAGE );
            }
        }
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
    
    private class SolverNameDocumentListener implements DocumentListener
    {
        @Override
        public void changedUpdate( DocumentEvent de )
        {
            checkSolverName();
        }

        @Override
        public void insertUpdate( DocumentEvent de )
        {
            checkSolverName();
        }

        @Override
        public void removeUpdate( DocumentEvent de )
        {
            checkSolverName();
        }
    }
    
    private class TakeOverSolverNameAction extends AbstractAction
    {
        private final String solverName;
        
        private TakeOverSolverNameAction( String solverName )
        {
            this.solverName = solverName;
        }
        
        @Override
        public void actionPerformed( ActionEvent ae )
        {
            solverNameTextField.setText( solverName );
            solverNameTextField.requestFocus();
        }
    }
}