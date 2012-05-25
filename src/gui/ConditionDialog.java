/* SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import javax.swing.*;

/**
 *
 * @author Ulrich Loup
 * @since 2012-03-12
 * @version 2012-03-12
 */
class ConditionDialog extends JDialog implements ActionListener, MouseListener
{
    /// write all module changes
    private final String OK_CMD = "ok";
    /// the condition to be edited
    String condition;
    // the text field where the condition is edited
    JTextArea conditionField;

    public ConditionDialog( JFrame parent, String condition )
    {
        super( parent, "Edit condition" );
        this.setLocationRelativeTo( parent );
        this.setResizable( true );

        this.condition = condition;

        this.conditionField = new JTextArea( this.condition, 32, 50 );
        this.getContentPane().add( BorderLayout.CENTER, new JScrollPane( this.conditionField, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED ) );

        JPanel okButtonPanel = new JPanel( new FlowLayout() );
        JButton okButton = new JButton( "OK" );
        okButton.addActionListener( this );
        okButton.setActionCommand( this.OK_CMD );
        okButtonPanel.add( okButton );
        this.getContentPane().add( BorderLayout.SOUTH, okButtonPanel );
    }

    public void actionPerformed( ActionEvent e )
    {
        String cmd = e.getActionCommand();
        if( cmd.startsWith( OK_CMD ) )
        {
        }
        this.setVisible( false );
        this.dispose();
    }

    @Override
    public void mouseClicked( MouseEvent e )
    {
    }

    @Override
    public void mouseEntered( MouseEvent e )
    {
    }

    @Override
    public void mouseExited( MouseEvent e )
    {
    }

    @Override
    public void mousePressed( MouseEvent e )
    {
        openContextMenu( e );
    }

    @Override
    public void mouseReleased( MouseEvent e )
    {
    }

    ///////////////////////
    // Auxiliary Methods //
    ///////////////////////
    /**
     * Opens a context menu in the text area.
     *
     * @param e
     */
    private void openContextMenu( MouseEvent e )
    {
    }

    private boolean checkConditionString( String input )
    {
        return input.matches( "" );
    }
}
