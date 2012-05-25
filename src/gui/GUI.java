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
import java.awt.Dimension;
import java.awt.event.*;
import java.io.File;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;

/**
 *
 * @author Ulrich Loup
 * @since 2012-02-07
 * @version 2012-03-11
 */
public class GUI extends JFrame implements WindowListener, ActionListener, MouseListener, ItemListener
{
    ///////////////
    // Constants //
    ///////////////
    /// path to the icon used for the GUI
    public static final String GUI_ICON_PATH = ".." + File.separator + ".." + File.separator + ".." + File.separator + "htdocs" + File.separator + "images" + File.separator + "icon.png";
    /// path to the help page
    public static final String HELP_PATH = "help.html";
    /// path to the icon for the About dialog
    public static final String ABOUT_TEXT = "<html><p>SMT-XRAT is a graphical user interface<br>to create and manage NRA solver modules<br>and solving strategies using these modules.</p><br>Support:<p>Ulrich Loup (<a href=\"mailto:loup@cs.rwth-aachen.de\">loup@cs.rwth-aachen.de</a>)<br>Florian Corzilius (<a href=\"mailto:corzilius@cs.rwth-aachen.de\">corzilius@cs.rwth-aachen.de</a>)</p></html>";
    /// path to the icon used for the About dialog
    public static final String ABOUT_ICON_PATH = ".." + File.separator + ".." + File.separator + ".." + File.separator + "htdocs" + File.separator + "images" + File.separator + "logoBig.png";
    /// write all module changes
    private final String ABOUT_CMD = "about";
    /// write all module changes
    private final String LICENSE_CMD = "license";
    /// write all module changes
    private final String HELP_CMD = "help";
    /// reload all modules
    private final String RELOAD_MODULES_CMD = "reloadmodules";
    /// reload all solvers
    private final String RELOAD_SOLVERS_CMD = "reloadsolvers";
    /// write all module changes
    private final String SAVE_MODULES_CMD = "savemodules";
    /// write all solver changes
    private final String SAVE_SOLVERS_CMD = "savesolvers";
    /// exit the gui
    private final String EXIT_CMD = "exit";
    /// switched solver
    private final String SWITCH_SOLVER_CMD = "switchsolver";
    /// add a module
    private final String ADD_MODULE_CMD = "addmodule";
    /// remove a module
    private final String REMOVE_MODULE_CMD = "removemodule";
    /// add a module
    private final String ADD_SOLVER_CMD = "addsolver";
    /// remove a module
    private final String REMOVE_SOLVER_CMD = "removesolver";
    /// add a module at the currently selected node
    private final String ADD_STRATEGYNODE_MODULE_CMD = "addstrategynodemodule";
    /// remove a module from the currently selected node
    private final String REMOVE_STRATEGYNODE_MODULE_CMD = "removestrategynodemodule";
    /// add a condition before the currently selected node
    private final String ADD_STRATEGYNODE_CONDITION_BEFORE_CMD = "addstrategynodeconditionbefore";
    /// add a condition after the currently selected node
    private final String ADD_STRATEGYNODE_CONDITION_AFTER_CMD = "addstrategynodeconditionafter";
    /// add a condition after the currently selected node
    private final String ADD_STRATEGYNODE_CONDITION_NEWLY_CMD = "addstrategynodeconditionnewly";
    /// remove a condition from the currently selected node
    private final String REMOVE_STRATEGYNODE_CONDITION_CMD = "removestrategynodecondition";
    ////////////////
    // Attributes //
    ////////////////
    private JMenu fileMenu, helpMenu, addModuleMenu, addConditionBeforeMenu, addConditionAfterMenu, addConditionNewlyMenu;
    private JPopupMenu moduleStrategyMenu;
    private JMenuItem removeModuleItem, removeConditionItem, aboutMenuItem, licenseMenuItem, helpMenuItem;
    private JList modulesList;
    private DefaultListModel modulesListModel;
    private JTree strategyTree;
    private DefaultTreeModel strategyTreeModel;
    private JComboBox solversComboBox;
    private JButton addModuleButton, removeModuleButton, addSolverButton, removeSolverButton;
    private HashMap<String, Strategy> strategiesPerSolver;
    private ArrayList<String> solversChanged;
    private ArrayList<String> solversRemoved;
    private ArrayList<String> conditions;
    private ArrayList<Strategy> newStrategies;
    private ArrayList<Module> modules, newModules, removedModules;
    private DefaultMutableTreeNode strategyRoot;
    private Strategy selectedStrategy;
    private boolean changedModules, changedSolvers, autoTreeUpdateEnabled;

    /////////////
    // Methods //
    /////////////
    /**
     * Main method.
     */
    public static void main( String[] args )
    {
        if( !IOTools.checkForProperLocation() )
        {
            System.out.println( "Current working directory: " + IOTools.CWD );
            System.out.println( IOTools.STRATEGY_SOURCE + " can not be found. SMT-XRAT can not be started! Abort." );
            return;
        }
        System.out.println( "Starting SMT-XRAT..." );
        new GUI();
        System.out.println( "... done." );
    }

    /**
     * Constructor.
     */
    private GUI()
    {
        super( "SMT-XRAT" );
        super.setIconImage( new ImageIcon( GUI_ICON_PATH ).getImage() );
        super.setDefaultCloseOperation( WindowConstants.DO_NOTHING_ON_CLOSE );
        addWindowListener( this );

        // make menue
        JMenuBar menuBar = new JMenuBar();

        this.fileMenu = new JMenu( "File" );
        this.fileMenu.setMnemonic( KeyEvent.VK_F );
        JMenuItem reloadModulesMenuItem = new JMenuItem( "Reload modules" );
        reloadModulesMenuItem.addActionListener( this );
        reloadModulesMenuItem.setActionCommand( RELOAD_MODULES_CMD );
        reloadModulesMenuItem.setMnemonic( KeyEvent.VK_M );
        this.fileMenu.add( reloadModulesMenuItem );
        JMenuItem reloadSolversMenuItem = new JMenuItem( "Reload solvers" );
        reloadSolversMenuItem.addActionListener( this );
        reloadSolversMenuItem.setActionCommand( RELOAD_SOLVERS_CMD );
        reloadSolversMenuItem.setMnemonic( KeyEvent.VK_S );
        this.fileMenu.add( reloadSolversMenuItem );
        JMenuItem saveModulesMenuItem = new JMenuItem( "Write module changes" );
        saveModulesMenuItem.addActionListener( this );
        saveModulesMenuItem.setActionCommand( SAVE_MODULES_CMD );
        saveModulesMenuItem.setMnemonic( KeyEvent.VK_D );
        saveModulesMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_M, InputEvent.CTRL_MASK ) );
        this.fileMenu.add( saveModulesMenuItem );
        JMenuItem saveSolversMenuItem = new JMenuItem( "Write solver changes" );
        saveSolversMenuItem.addActionListener( this );
        saveSolversMenuItem.setActionCommand( SAVE_SOLVERS_CMD );
        saveSolversMenuItem.setMnemonic( KeyEvent.VK_L );
        saveSolversMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_O, InputEvent.CTRL_MASK ) );
        this.fileMenu.add( saveSolversMenuItem );
        JMenuItem exitMenuItem = new JMenuItem( "Exit" );
        exitMenuItem.addActionListener( this );
        exitMenuItem.setActionCommand( EXIT_CMD );
        exitMenuItem.setMnemonic( KeyEvent.VK_X );
        exitMenuItem.setAccelerator( KeyStroke.getKeyStroke( KeyEvent.VK_Q, InputEvent.CTRL_MASK ) );
        fileMenu.add( exitMenuItem );
        menuBar.add( fileMenu );

        this.helpMenu = new JMenu( "Help" );
        this.helpMenu.setMnemonic( KeyEvent.VK_H );
        this.helpMenuItem = new JMenuItem( "Help" );
        this.helpMenuItem.addActionListener( this );
        this.helpMenuItem.setActionCommand( HELP_CMD );
        this.helpMenuItem.setMnemonic( KeyEvent.VK_H );
        this.helpMenu.add( this.helpMenuItem );
        this.licenseMenuItem = new JMenuItem( "License" );
        this.licenseMenuItem.addActionListener( this );
        this.licenseMenuItem.setActionCommand( LICENSE_CMD );
        this.licenseMenuItem.setMnemonic( KeyEvent.VK_L );
        this.helpMenu.add( this.licenseMenuItem );
        this.aboutMenuItem = new JMenuItem( "About" );
        this.aboutMenuItem.addActionListener( this );
        this.aboutMenuItem.setActionCommand( ABOUT_CMD );
        this.aboutMenuItem.setMnemonic( KeyEvent.VK_A );
        this.helpMenu.add( this.aboutMenuItem );
        menuBar.add( helpMenu );

        setJMenuBar( menuBar );
        this.addModuleMenu = new JMenu( "Add module" );
        this.addModuleMenu.setActionCommand( ADD_STRATEGYNODE_MODULE_CMD );
        this.addModuleMenu.addActionListener( this );
        this.removeModuleItem = new JMenuItem( "Remove module" );
        this.removeModuleItem.setActionCommand( REMOVE_STRATEGYNODE_MODULE_CMD );
        this.removeModuleItem.addActionListener( this );
        this.addConditionBeforeMenu = new JMenu( "Insert condition before" );
        this.addConditionAfterMenu = new JMenu( "Insert condition after" );
        this.addConditionNewlyMenu = new JMenu( "Add condition" );
        this.removeConditionItem = new JMenuItem( "Remove condition" );
        this.removeConditionItem.setActionCommand( REMOVE_STRATEGYNODE_CONDITION_CMD );
        this.removeConditionItem.addActionListener( this );

        // make module part of the GUI
        Box modulesBox = Box.createVerticalBox();
        modulesBox.setBorder( BorderFactory.createCompoundBorder(
            BorderFactory.createCompoundBorder(
            BorderFactory.createTitledBorder( "Modules" ),
            BorderFactory.createEmptyBorder( 4, 3, 4, 3 ) ),
            modulesBox.getBorder() ) );
        this.newModules = new ArrayList<Module>();
        this.removedModules = new ArrayList<Module>();
        this.modulesListModel = new DefaultListModel();
        this.modulesList = new JList( this.modulesListModel );
        this.modulesList.setSelectionMode( ListSelectionModel.SINGLE_SELECTION );
        modulesBox.add( new JScrollPane( this.modulesList, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED ) );
        JPanel modulesButtonsPanel = new JPanel();
        this.addModuleButton = new JButton( "Add module" );
        this.addModuleButton.setActionCommand( ADD_MODULE_CMD );
        this.addModuleButton.addActionListener( this );
        modulesButtonsPanel.add( BorderLayout.WEST, this.addModuleButton );
        this.removeModuleButton = new JButton( "Remove module" );
        this.removeModuleButton.addActionListener( this );
        this.removeModuleButton.setActionCommand( REMOVE_MODULE_CMD );
        modulesButtonsPanel.add( BorderLayout.WEST, this.removeModuleButton );
        modulesBox.add( modulesButtonsPanel );

        // make solver part of the GUI
        Box solversBox = Box.createVerticalBox();
        solversBox.setBorder( BorderFactory.createCompoundBorder(
            BorderFactory.createCompoundBorder(
            BorderFactory.createTitledBorder( "Solvers" ),
            BorderFactory.createEmptyBorder( 4, 3, 4, 3 ) ),
            solversBox.getBorder() ) );
        this.solversComboBox = new JComboBox();
        this.solversComboBox.addActionListener( this );
        this.solversComboBox.setActionCommand( SWITCH_SOLVER_CMD );
        solversBox.add( this.solversComboBox );
        solversBox.add( new JSeparator( JSeparator.HORIZONTAL ) );
        this.strategyRoot = new DefaultMutableTreeNode();
        this.strategyTreeModel = new DefaultTreeModel( strategyRoot, true );
        this.strategyTree = new JTree( this.strategyTreeModel );
        this.strategyTree.setEditable( false );
        this.strategyTree.getSelectionModel().setSelectionMode( TreeSelectionModel.SINGLE_TREE_SELECTION );
        this.strategyTree.setRootVisible( false );
        this.strategyTree.setShowsRootHandles( false );
        this.strategyTree.addMouseListener( this );
        solversBox.add( new JScrollPane( this.strategyTree, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED ) );
        JPanel solversButtonsPanel = new JPanel();
        this.addSolverButton = new JButton( "Add solver" );
        this.addSolverButton.setActionCommand( ADD_SOLVER_CMD );
        this.addSolverButton.addActionListener( this );
        solversButtonsPanel.add( BorderLayout.WEST, this.addSolverButton );
        this.removeSolverButton = new JButton( "Remove solver" );
        this.removeSolverButton.addActionListener( this );
        this.removeSolverButton.setActionCommand( REMOVE_SOLVER_CMD );
        solversButtonsPanel.add( BorderLayout.WEST, this.removeSolverButton );
        solversBox.add( solversButtonsPanel );

        // add components to frame
        getContentPane().add( BorderLayout.WEST, modulesBox );
        getContentPane().add( BorderLayout.EAST, solversBox );

        // read directory contents
        updateModules();
        updateSolvers();

        // initially, there is nothing changed
        this.changedModules = false;
        this.changedSolvers = false;
        this.newStrategies = new ArrayList<Strategy>();

        // show the frame
        
        pack();
        setVisible( true );
    }

    ///////////////
    // Listeners //
    ///////////////
    @Override
    public void windowActivated( WindowEvent e )
    {
    }

    @Override
    public void windowClosed( WindowEvent e )
    {
    }

    @Override
    public void windowDeactivated( WindowEvent e )
    {
    }

    @Override
    public void windowDeiconified( WindowEvent e )
    {
    }

    @Override
    public void windowIconified( WindowEvent e )
    {
    }

    @Override
    public void windowOpened( WindowEvent e )
    {
    }

    @Override
    public void windowClosing( WindowEvent e )
    {
        // save changes if any?
        if( this.changedModules || this.changedSolvers )
        {
            if( JOptionPane.showConfirmDialog( this, "There are unsaved changes. Do you want to write them to the source before leaving?", "Question", JOptionPane.YES_NO_OPTION ) == JOptionPane.YES_OPTION )
            {
                writeModuleChanges();
                if( !writeSolverChanges() ) // do not exit in case there is an erroneous strategy for one solver defined
                    return;
            }
        }
        // exit
        setVisible( false );
        dispose();
    }

    public void actionPerformed( ActionEvent e )
    {
        String cmd = e.getActionCommand();
        try
        {
            if( cmd.startsWith( RELOAD_MODULES_CMD ) )
            {
                if( this.changedModules )
                { // save changes
                    if( JOptionPane.showConfirmDialog( this, "There are unsaved changes. Do you want to write them to the source before reloading?", "Question", JOptionPane.YES_NO_OPTION ) == JOptionPane.YES_OPTION )
                    {
                        writeModuleChanges();
                    }
                    else
                        JOptionPane.showMessageDialog( this, "All module changes will be undone.", "Warning", JOptionPane.WARNING_MESSAGE );
                }
                updateModules();
                this.changedModules = false;
            }
            else if( cmd.startsWith( RELOAD_SOLVERS_CMD ) )
            {
                if( this.changedSolvers )
                { // save changes
                    if( JOptionPane.showConfirmDialog( this, "There are unsaved changes. Do you want to write them to the source before reloading?", "Question", JOptionPane.YES_NO_OPTION ) == JOptionPane.YES_OPTION )
                    {
                        if( !writeSolverChanges() )
                            return;
                    }
                    else
                        JOptionPane.showMessageDialog( this, "All solver changes will be undone.", "Warning", JOptionPane.WARNING_MESSAGE );
                }
                updateSolvers();
                this.changedSolvers = false;
            }
            else if( cmd.startsWith( SAVE_MODULES_CMD ) )
            {
                if( !this.changedModules )
                    return;
                writeModuleChanges();
                this.changedModules = this.newStrategies.isEmpty();
            }
            else if( cmd.startsWith( SAVE_SOLVERS_CMD ) )
            {
                if( !this.changedSolvers )
                    return;
                this.changedSolvers = !writeSolverChanges();
            }
            else if( cmd.startsWith( EXIT_CMD ) )
            {
                windowClosing( null );
            }
            else if( cmd.startsWith( HELP_CMD ) )
            {
                JEditorPane helpPane = new JEditorPane();
                helpPane.setEditable( false );
                java.net.URL helpURL = GUI.class.getResource( HELP_PATH );
                if( helpURL != null )
                {
                    try
                    {
                        helpPane.setPage( helpURL );
                        JScrollPane helpScrollPane = new JScrollPane( helpPane, ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED );
                        helpScrollPane.setPreferredSize( new Dimension( 640, 480 ) );
                        JOptionPane.showOptionDialog( this, null, "SMT-XRAT Help", JOptionPane.NO_OPTION, JOptionPane.PLAIN_MESSAGE, null, new Object[]
                            {
                                helpScrollPane
                            }, null );
                    }
                    catch( Exception ex )
                    {
                        JOptionPane.showMessageDialog( this, "The help page can not be displayed.", "Error", JOptionPane.ERROR_MESSAGE );
                    }
                }
                else
                    JOptionPane.showMessageDialog( this, "The help page help.html was not found.", "Error", JOptionPane.ERROR_MESSAGE );
            }
            else if( cmd.startsWith( LICENSE_CMD ) )
            {
                new LicenseDialog( this );
            }
            else if( cmd.startsWith( ABOUT_CMD ) )
            {
                JOptionPane.showOptionDialog( this, this.ABOUT_TEXT, "About SMT-XRAT", JOptionPane.NO_OPTION, JOptionPane.INFORMATION_MESSAGE, new ImageIcon( ABOUT_ICON_PATH ), new Object[]
                    {
                        "OK"
                    }, null );
            }
            else if( cmd.startsWith( SWITCH_SOLVER_CMD ) )
            {
                if( this.autoTreeUpdateEnabled )
                    updateStrategyTree();
            }
            else if( cmd.startsWith( ADD_SOLVER_CMD ) )
            {
//                JOptionPane.showMessageDialog( this, "This function will soon be available in a future release.", "Information", JOptionPane.INFORMATION_MESSAGE );
                String solverName = JOptionPane.showInputDialog( this, "Please enter the name of the new solver.", "MySolver" );
                if( solverName == null || solverName.isEmpty() )
                    return;
                while( !checkInputString( solverName ) )
                {
                    solverName = JOptionPane.showInputDialog( this, "<html><font color=green>" + solverName + " invalid as solver name.</font><br>Please use a valid C++ identifier.", solverName );
                    if( solverName == null || solverName.isEmpty() )
                        return;
                    if( this.strategiesPerSolver.containsKey( solverName ) )
                        solverName = JOptionPane.showInputDialog( this, "<html><font color=green>" + solverName + " does already denote a solver.</font><br>Please choose another name.", solverName );
                }
                this.solversChanged.add( solverName );
                this.strategiesPerSolver.put( solverName, new Strategy( "", false ) ); // initial root node
                this.autoTreeUpdateEnabled = false;
                this.solversComboBox.addItem( solverName );
                this.solversComboBox.updateUI();
                this.solversComboBox.setSelectedIndex( this.solversComboBox.getItemCount() - 1 );
                this.updateStrategyTree();
                this.autoTreeUpdateEnabled = true;
                this.changedSolvers = true;
            }
            else if( cmd.startsWith( REMOVE_SOLVER_CMD ) )
            {
//                JOptionPane.showMessageDialog( this, "This function will soon be available in a future release.", "Information", JOptionPane.INFORMATION_MESSAGE );
                int selection = this.solversComboBox.getSelectedIndex();
                if( selection == -1 )
                    return;
                String solverName = this.solversComboBox.getSelectedItem().toString();
                if( JOptionPane.showConfirmDialog( this, "<html>Do you really want to remove the solver: " + solverName + "</html>", "Question", JOptionPane.YES_NO_OPTION ) == JOptionPane.YES_OPTION )
                {
                    solversRemoved.add( this.solversComboBox.getSelectedItem().toString() );
                    this.solversComboBox.removeItemAt( selection );
                    this.updateStrategyTree();
                    this.changedSolvers = true;
                }
            }
            else if( cmd.startsWith( ADD_STRATEGYNODE_MODULE_CMD ) )
            {
                if( this.selectedStrategy == null )
                    return;
                if( this.selectedStrategy.getChildCount() != 0 )
                {
                    JOptionPane.showMessageDialog( this, "<html>SMT-RAT does not support parallel module calls yet.<br>No module added.</html>", "Information", JOptionPane.INFORMATION_MESSAGE );
                    return;
                }
                Strategy newStrategy = new Strategy( this.modules.get( Integer.parseInt( cmd.replaceFirst( ADD_STRATEGYNODE_MODULE_CMD, "" ) ) ) );
                // update model
                this.strategyTreeModel.insertNodeInto( newStrategy, this.selectedStrategy, this.selectedStrategy.getChildCount() );
                for( int r = 0; r != this.strategyTree.getRowCount(); ++r )
                    if( !this.strategyTree.isExpanded( r ) )
                        this.strategyTree.expandRow( r );
                if( !this.solversChanged.contains( this.solversComboBox.getSelectedItem().toString() ) )
                    this.solversChanged.add( this.solversComboBox.getSelectedItem().toString() );
                this.changedSolvers = true;
            }
            else if( cmd.startsWith( REMOVE_STRATEGYNODE_MODULE_CMD ) )
            {
                if( this.selectedStrategy == null )
                    return;
                // update model
                this.strategyTreeModel.removeNodeFromParent( this.selectedStrategy );
                if( !this.solversChanged.contains( this.solversComboBox.getSelectedItem().toString() ) )
                    this.solversChanged.add( this.solversComboBox.getSelectedItem().toString() );
                this.changedSolvers = true;
            }
            else if( cmd.startsWith( ADD_STRATEGYNODE_CONDITION_NEWLY_CMD ) )
            {
                Strategy newStrategy = new Strategy( this.conditions.get( Integer.parseInt( cmd.replaceFirst( ADD_STRATEGYNODE_CONDITION_NEWLY_CMD, "" ) ) ) );
                this.strategyTreeModel.insertNodeInto( newStrategy, this.strategyRoot, this.strategyRoot.getChildCount() );
                if( !this.solversChanged.contains( this.solversComboBox.getSelectedItem().toString() ) )
                    this.solversChanged.add( this.solversComboBox.getSelectedItem().toString() );
                this.changedSolvers = true;
            }
            else if( cmd.startsWith( ADD_STRATEGYNODE_CONDITION_BEFORE_CMD ) )
            {
                if( this.selectedStrategy == null )
                    return;
                Strategy newStrategy = new Strategy( this.conditions.get( Integer.parseInt( cmd.replaceFirst( ADD_STRATEGYNODE_CONDITION_BEFORE_CMD, "" ) ) ) );
                // update model
                this.strategyTreeModel.insertNodeInto( newStrategy, this.strategyRoot, this.strategyTreeModel.getIndexOfChild( this.strategyRoot, this.selectedStrategy ) );
                if( !this.solversChanged.contains( this.solversComboBox.getSelectedItem().toString() ) )
                    this.solversChanged.add( this.solversComboBox.getSelectedItem().toString() );
                this.changedSolvers = true;
            }
            else if( cmd.startsWith( ADD_STRATEGYNODE_CONDITION_AFTER_CMD ) )
            {
                if( this.selectedStrategy == null )
                    return;
                Strategy newStrategy = new Strategy( this.conditions.get( Integer.parseInt( cmd.replaceFirst( ADD_STRATEGYNODE_CONDITION_AFTER_CMD, "" ) ) ) );
                // update model
                this.strategyTreeModel.insertNodeInto( newStrategy, this.strategyRoot, this.strategyTreeModel.getIndexOfChild( this.strategyRoot, this.selectedStrategy ) + 1 );
//                // update data
//                this.strategiesPerSolver.get( this.solversComboBox.getSelectedItem().toString() ).addAfter( newStrategy, this.selectedStrategy );
                if( !this.solversChanged.contains( this.solversComboBox.getSelectedItem().toString() ) )
                    this.solversChanged.add( this.solversComboBox.getSelectedItem().toString() );
                this.changedSolvers = true;
            }
            else if( cmd.startsWith( REMOVE_STRATEGYNODE_CONDITION_CMD ) )
            {
                if( this.selectedStrategy == null )
                    return;
                if( this.selectedStrategy.getChildCount() > 0 && JOptionPane.showConfirmDialog( this, "All module calls entailed by this condition are also deleted. Are you sure?", "Question", JOptionPane.YES_NO_OPTION ) != JOptionPane.YES_OPTION )
                    return;
                // update model
                this.strategyTreeModel.removeNodeFromParent( this.selectedStrategy );
                if( !this.solversChanged.contains( this.solversComboBox.getSelectedItem().toString() ) )
                    this.solversChanged.add( this.solversComboBox.getSelectedItem().toString() );
                this.changedSolvers = true;
            }
            else if( cmd.startsWith( ADD_MODULE_CMD ) )
            {
                String moduleName = JOptionPane.showInputDialog( this, "Please enter the name of the new module.", "MyModule" );
                if( moduleName == null || moduleName.isEmpty() )
                    return;
                Module module = new Module( moduleName );
                while( !checkInputString( moduleName ) )
                {
                    moduleName = JOptionPane.showInputDialog( this, "<html><font color=green>" + moduleName + " invalid as module name.</font><br>Please use a valid C++ identifier.", moduleName );
                    if( moduleName == null || moduleName.isEmpty() )
                        return;
                    module = new Module( moduleName );
                    if( this.modulesListModel.contains( module ) )
                        moduleName = JOptionPane.showInputDialog( this, "<html><font color=green>" + moduleName + " does already denote a module.</font><br>Please choose another name.", moduleName );
                }
                this.newModules.add( module );
                this.modulesListModel.addElement( module );
                this.changedModules = true;
            }
            else if( cmd.startsWith( REMOVE_MODULE_CMD ) )
            {
                int selection = this.modulesList.getSelectedIndex();
                if( selection == -1 )
                    return;
                String moduleName = this.modulesListModel.get( selection ).toString().replaceAll( "html", "center" );
                if( JOptionPane.showConfirmDialog( this, "<html>Do you really want to remove the module: " + moduleName + "</html>", "Question", JOptionPane.YES_NO_OPTION ) == JOptionPane.YES_OPTION )
                {
                    if( selection < this.modules.size() )
                    { // module was already present before the start and has possibly an implementation

                        if( JOptionPane.showConfirmDialog( this, "<html>Are you sure? The module " + moduleName + " is already implemented!</html>", "Question", JOptionPane.YES_NO_OPTION ) != JOptionPane.YES_OPTION )
                            return;
                        this.removedModules.add( this.modules.remove( selection ) );
                        JOptionPane.showMessageDialog( this, "<html>The module " + moduleName + " will be completely removed from source when writing the changes.</html>", "Warning", JOptionPane.WARNING_MESSAGE );
                    }
                    else
                        this.newModules.remove( selection - this.modules.size() );
                    this.modulesListModel.remove( selection );
                    this.changedModules = true;
                }
            }
        }
        catch( Exception ex )
        {
            JOptionPane.showMessageDialog( this, ex.toString(), "Error", JOptionPane.ERROR_MESSAGE );
        }
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

    public void itemStateChanged( ItemEvent e )
    {
        if( this.autoTreeUpdateEnabled )
            updateStrategyTree();
    }

    ///////////////////////
    // Auxiliary Methods //
    ///////////////////////
    /**
     * Opens a context menu in the strategy tree.
     *
     * @param e
     */
    private void openContextMenu( MouseEvent e )
    {
        if( !e.isPopupTrigger() ) // only allow "right clicks"
            return;
        int row = this.strategyTree.getClosestRowForLocation( e.getX(), e.getY() );
        if( row != -1 )
        {
            TreePath path = this.strategyTree.getPathForLocation( e.getX(), e.getY() );
            if( path == null || !(path.getLastPathComponent() instanceof Strategy) )
                return;
            this.selectedStrategy = (Strategy) path.getLastPathComponent();
            this.moduleStrategyMenu = new JPopupMenu();
            if( this.selectedStrategy.isCondition() )
            { // open context menu for a condition node, i.e., offer options for module nodes
                this.addModuleMenu.removeAll();
                for( int i = 0; i != this.modules.size(); ++i )
                {
                    JMenuItem item = new JMenuItem( this.modules.get( i ).toString() );
                    item.setActionCommand( ADD_STRATEGYNODE_MODULE_CMD + i );
                    item.addActionListener( this );
                    this.addModuleMenu.add( item );
                }
                this.moduleStrategyMenu.add( this.addModuleMenu );

                this.addConditionBeforeMenu.removeAll();
                for( int i = 0; i != this.conditions.size(); ++i )
                {
                    JMenuItem item = new JMenuItem( this.conditions.get( i ) );
                    item.setActionCommand( ADD_STRATEGYNODE_CONDITION_BEFORE_CMD + i );
                    item.addActionListener( this );
                    this.addConditionBeforeMenu.add( item );
                }
                this.moduleStrategyMenu.add( this.addConditionBeforeMenu );

                this.addConditionAfterMenu.removeAll();
                for( int i = 0; i != this.conditions.size(); ++i )
                {
                    JMenuItem item = new JMenuItem( this.conditions.get( i ) );
                    item.setActionCommand( ADD_STRATEGYNODE_CONDITION_AFTER_CMD + i );
                    item.addActionListener( this );
                    this.addConditionAfterMenu.add( item );
                }
                this.moduleStrategyMenu.add( this.addConditionAfterMenu );
                this.moduleStrategyMenu.add( this.removeConditionItem );
            }
            else
            {
                this.moduleStrategyMenu.add( this.removeModuleItem );
            }
            this.moduleStrategyMenu.show( e.getComponent(), e.getX(), e.getY() );
        }
        else
        { // open context menu to add a new condition at the end of the conditions list
            this.moduleStrategyMenu = new JPopupMenu();
            this.addConditionNewlyMenu.removeAll();
            for( int i = 0; i != this.conditions.size(); ++i )
            {
                JMenuItem item = new JMenuItem( this.conditions.get( i ) );
                item.setActionCommand( ADD_STRATEGYNODE_CONDITION_NEWLY_CMD + i );
                item.addActionListener( this );
                this.addConditionNewlyMenu.add( item );
            }
            this.moduleStrategyMenu.add( this.addConditionNewlyMenu );
            this.moduleStrategyMenu.show( e.getComponent(), e.getX(), e.getY() );
        }
    }

    /**
     * Re-reads the module information from the source and updates the GUI.
     */
    private void updateModules()
    {
        this.modulesList.setEnabled( false );
        this.modulesListModel.removeAllElements();
        this.modules = IOTools.readModules();
        for( Module module : this.modules )
        {
            this.modulesListModel.addElement( "<html><font color=green>" + module + "</font></html>" );
        }
        for( Module module : this.newModules )
        {
            this.modulesListModel.addElement( module );
        }
        this.modulesList.updateUI();
        this.modulesList.setEnabled( true );
    }

    /**
     * Re-reads the solver information from the source and updates the GUI.
     */
    private void updateSolvers()
    {
        this.autoTreeUpdateEnabled = false;
        this.solversComboBox.setEnabled( false );
        this.conditions = IOTools.readConditions();
        this.strategiesPerSolver = IOTools.readSolvers( this.conditions, this.modules );
        int previousSelection = this.solversComboBox.getSelectedIndex();
        previousSelection = previousSelection == -1 ? 0 : previousSelection;
        this.solversComboBox.removeAllItems();
        for( String solver : this.strategiesPerSolver.keySet() )
            this.solversComboBox.addItem( solver );
        this.solversComboBox.updateUI();
        this.solversComboBox.setSelectedIndex( previousSelection );
        updateStrategyTree();
        this.solversChanged = new ArrayList<String>();
        this.solversRemoved = new ArrayList<String>();
        this.solversComboBox.setEnabled( true );
        this.autoTreeUpdateEnabled = true;
    }

    /**
     * Redraws the the tree representing the strategy of the selected solver.
     */
    private void updateStrategyTree()
    {
        if( this.solversComboBox.getItemCount() == 0 )
            return;
        this.strategyTree.setEnabled( false );
        this.strategyRoot = this.strategiesPerSolver.get( this.solversComboBox.getSelectedItem().toString() );
        this.strategyTreeModel.setRoot( this.strategyRoot );
        for( int r = 0; r != this.strategyTree.getRowCount(); ++r )
            this.strategyTree.expandRow( r );
        this.strategyTree.setEnabled( true );
    }

    /**
     * Checks if the given string is a valid C++ identifier.
     *
     * @param input
     * @return true if the given string is a valid C++ identifier, false otherwise
     */
    private boolean checkInputString( String input )
    {
        return input.matches( "[a-zA-Z_-]*" );
    }

    /**
     * Checks if the given solver defines a syntactically correct strategy, i.e., each condition entails exactly one module call.
     *
     * @param solver
     * @return true if each condition entails exactly one module call, false otherwise
     */
    private boolean checkSolverStrategy( String solver )
    {
        for( Enumeration e = this.strategiesPerSolver.get( solver ).children(); e.hasMoreElements(); )
        {
            Strategy strategy = (Strategy) e.nextElement();
            if( !strategy.isCondition()
                || (strategy.isCondition() && (strategy.getChildCount() != 1
                                               || (strategy.getChildCount() == 1 && strategy.getFirstChild() != null && strategy.getFirstChild().isCondition()))) )
                return false;
        }
        return true;
    }

    /**
     * Writes all module-related changes to the source, whether adding or deleting.
     */
    private boolean writeModuleChanges()
    {
        // remove new modules from list model
        for( int i = this.modules.size(); i < this.modules.size() + this.newModules.size() - this.removedModules.size(); ++i )
            this.modulesListModel.remove( i );
        // add new modules to source, change list entry and remove from new list
        ArrayList<Module> newNewModules = new ArrayList<Module>( this.newModules.size() );
        for( Module module : this.newModules )
        {
            try
            {
                IOTools.writeModule( module, true ); // add the module
                this.modules.add( module );
                this.modulesListModel.addElement( "<html><font color=green>" + module + "</font></html>" );
                JOptionPane.showMessageDialog( this, "<html>The module <em>" + module + "</em> was generated in <code>" + IOTools.MODULES_SOURCE_DIR.getPath() + "</code>.<br>You may implement the respective files <code>" + module + ".{h,vpp}</code>.</html>", "Information", JOptionPane.INFORMATION_MESSAGE );
            }
            catch( Exception ex )
            {
                newNewModules.add( module ); // do not add module to modules, keep it in newModules
                JOptionPane.showMessageDialog( this, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
            }
        }
        this.newModules = newNewModules;
        // remove deleted modules from source
        for( Module module : this.removedModules )
        {
            try
            {
                IOTools.writeModule( module, false ); // remove the module
                JOptionPane.showMessageDialog( this, "<html>The module <em>" + module + "</em> was removed from source.", "Information", JOptionPane.INFORMATION_MESSAGE );
            }
            catch( Exception ex )
            {
                JOptionPane.showMessageDialog( this, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
            }
        }
        this.removedModules = new ArrayList<Module>();
        return true;
    }

    /**
     * Writes all solver-related changes to the source, whether adding or deleting.
     */
    private boolean writeSolverChanges()
    {
        // verify solver strategies
        for( String solver : this.solversChanged )
        {
            if( !checkSolverStrategy( solver ) )
            {
                JOptionPane.showMessageDialog( this, "<html>The strategy of solver <em>" + solver + "</em> is erroneous. The changes are not written.", "Error", JOptionPane.ERROR_MESSAGE );
                return false;
            }
        }
        // add/modify solvers
        for( String solver : this.solversChanged )
        {
            try
            {
                IOTools.writeSolver( solver, this.strategiesPerSolver.get( solver ), true );
                JOptionPane.showMessageDialog( this, "<html>The solver <em>" + solver + "</em> was generated as <code>" + IOTools.STRATEGY_SOURCE_DIR.getPath() + File.separator + solver + ".{h,vpp}</code>.</html>", "Information", JOptionPane.INFORMATION_MESSAGE );
            }
            catch( Exception ex )
            {
                JOptionPane.showMessageDialog( this, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
            }
        }
        this.solversChanged = new ArrayList<String>();
        // delete solvers
        for( String solver : this.solversRemoved )
        {
            try
            {
                IOTools.writeSolver( solver, this.strategiesPerSolver.get( solver ), false );
                this.strategiesPerSolver.remove( solver );
                JOptionPane.showMessageDialog( this, "<html>The solver <em>" + solver + "</em> was removed from source.", "Information", JOptionPane.INFORMATION_MESSAGE );
            }
            catch( Exception ex )
            {
                JOptionPane.showMessageDialog( this, ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE );
            }

        }
        this.solversRemoved = new ArrayList<String>();
        return true;
    }
}
