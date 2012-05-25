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

import java.io.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 *
 * @author Ulrich Loup
 * @since 2012-02-07
 * @version 2012-03-08
 */
public class IOTools
{
    public static final File STRATEGY_SOURCE_DIR = new File( ".." + File.separator + ".." + File.separator + ".." + File.separator + "src" );
    public static final File MODULES_SOURCE_DIR = new File( STRATEGY_SOURCE_DIR.getPath() + File.separator + "modules" );
    public static final File STRATEGY_SOURCE = new File( STRATEGY_SOURCE_DIR.getPath() + File.separator + "Manager.h" );
    public static final File STRATEGY_IMPLEMENTATION = new File( STRATEGY_SOURCE_DIR.getPath() + File.separator + "Manager.cpp" );
    public static final File STRATEGY_BUILDFILE = new File( STRATEGY_SOURCE_DIR.getPath() + File.separator + "CMakeLists.txt" );
    public static final File CONDITIONS_SOURCE = new File( STRATEGY_SOURCE_DIR.getPath() + File.separator + "Formula.h" );
    public static final File CONDITIONS_IMPLEMENTATION = new File( STRATEGY_SOURCE_DIR.getPath() + File.separator + "Formula.cpp" );
    public static final File MODULES_SOURCE = new File( MODULES_SOURCE_DIR.getPath() + File.separator + "Modules.h" );
    public static final String MODULETYPE = "ModuleType";
    public static final String MODULECLASS = "Module";
    public static final String CONDITIONCLASS = "Condition";
    public static final String MANAGRECLASS = "Manager";
    public static final File MODULETYPE_SOURCE = new File( STRATEGY_SOURCE_DIR.getPath() + File.separator + "ModuleType.h" );
    public static final File CWD = new File( System.getProperty( "user.dir" ) );

    /**
     * Check whether StrategySource is found relative to the current working directory CWD.
     *
     * @return
     */
    public static boolean checkForProperLocation()
    {
        if( STRATEGY_SOURCE.exists() )
            return true;
        return false;
    }

    /**
     * Scans the file ModuleTypes.h for potential modules. For each type, the directory modules is searched for a class, derived from Module,
     * containing the module type. The results of this search are returned.
     *
     * @return operational Modules available
     */
    public static ArrayList<Module> readModules()
    {
        ArrayList<Module> modules = new ArrayList<Module>();
        BufferedReader readFile = openFile( MODULETYPE_SOURCE );
        String definition = "";
        // search line with definition of ModuleTypes
        Pattern definitionStart = Pattern.compile( ".*enum\\s*" + MODULETYPE + "\\s*", Pattern.COMMENTS + Pattern.DOTALL );
        while( (definition = readLine( readFile )) != null && !definitionStart.matcher( definition ).matches() );
        if( definition == null )
            return modules;
        // concatenate all lines belonging to the ModuleType definition, while removing the comments
        String line = "";
        while( (line = readLine( readFile )) != null && !line.contains( "}" ) )
        {
            // remove comments
            int offset = line.indexOf( "//" );
            if( offset != -1 )
                line = line.substring( 0, offset );
            offset = line.indexOf( "/*" );
            if( offset != -1 )
                line = line.substring( 0, offset );
            offset = line.indexOf( "*/" );
            if( offset != -1 && offset < line.length() - 1 )
                line = line.substring( offset + 2 );
            definition += line;
        }
        if( line != null )
            definition += line;
        closeFile( readFile );
        // remove leading and trailing braces
        definition = definition.substring( definition.indexOf( "{" ) + 1, definition.indexOf( "}" ) );
        // parse module types from definition
        String[] moduleTypes = definition.split( "," );
        if( moduleTypes.length == 0 )
            return modules;
        // create search pattern for module class definition
        for( int i = 0; i != moduleTypes.length; ++i )
            moduleTypes[i] = moduleTypes[i].trim();
        String modulesPattern = moduleTypes[0];
        for( int i = 1; i != moduleTypes.length; ++i )
            modulesPattern += "|" + moduleTypes[i].trim();
        Pattern moduleClassExtension = Pattern.compile( ".*public\\s*" + MODULECLASS + "[^F]*", Pattern.COMMENTS + Pattern.DOTALL );
        Pattern moduleTypeDefinition = Pattern.compile( ".*mModuleType\\s*=\\s*(" + modulesPattern + ")" + ".*", Pattern.COMMENTS + Pattern.DOTALL );
        for( File f : MODULES_SOURCE_DIR.listFiles() )
        {
            String name = f.getName();
            if( name.endsWith( ".h" ) )
            {
                if( name.length() <= 2 )
                    continue;
                name = name.substring( 0, name.length() - 2 ); // remove .h extension
                // does the file contain a class definition extending Module
                readFile = openFile( f );
                line = "";
                while( (line = readLine( readFile )) != null && !line.contains( "class " + name ) );
                if( line == null )
                    continue;
                while( line != null && !moduleClassExtension.matcher( line ).matches() )
                    line = readLine( readFile );
                closeFile( readFile );
                if( line == null )
                    continue;
                // if yes, see if a cpp file is existing and check it for the proper type
                f = new File( MODULES_SOURCE_DIR + File.separator + name + ".cpp" );
                if( !f.exists() )
                    continue;
                readFile = openFile( f );
                line = "";
                while( (line = readLine( readFile )) != null && !moduleTypeDefinition.matcher( line ).matches() );
                if( line == null )
                {
                    System.err.println( "WARNING: Though " + name + " defines a proper " + MODULETYPE + ", " + f + " does not implement it." );
                    continue;
                }
                // search correct module type (first match)
                int i = 0;
                for( ; i != moduleTypes.length; ++i )
                    if( moduleTypes[i].contains( name ) )
                    {
                        modules.add( new Module( name, moduleTypes[i] ) );
                        break;
                    }
                if( i == moduleTypes.length ) // if not found, take name as type
                    modules.add( new Module( name, name ) );
                closeFile( readFile );
            }
        }
        return modules;
    }

    /**
     * Scans the file Formula.h for potential conditions.
     *
     * @return conditions usable in a strategy
     */
    public static ArrayList<String> readConditions()
    {
        ArrayList<String> conditions = new ArrayList<String>();
        BufferedReader readFile = openFile( CONDITIONS_SOURCE );
        String line = "";
        // search lines of condition definition
        Pattern definitionStart = Pattern.compile( ".*static\\s*const\\s*" + CONDITIONCLASS + ".*=.*", Pattern.COMMENTS + Pattern.DOTALL );
        while( (line = readLine( readFile )) != null )
        {
            while( line != null && !definitionStart.matcher( line ).matches() )
                line = readLine( readFile );
            if( line == null )
                break;
            String condition = line;
            int beginOffset = line.indexOf( CONDITIONCLASS + " " ) + CONDITIONCLASS.length() + 1;
            int endOffset = beginOffset;
            while( line != null && (endOffset = condition.indexOf( "=", endOffset )) == -1 )
            {
                line = readLine( readFile );
                condition += line;
            }
            if( line == null )
                break;
            // proper condition definition found
            conditions.add( condition.substring( beginOffset, endOffset ).trim() );
        }
        closeFile( readFile );
        if( conditions.isEmpty() )
            System.err.println( "WARNING: No condition found in " + CONDITIONS_SOURCE + "." );
        return conditions;
    }

    /**
     * Read the solvers available in the source.
     *
     * @param conditions
     * @return a map "Solver name" -> "Strategy"
     */
    public static HashMap<String, Strategy> readSolvers( ArrayList<String> conditions, ArrayList<Module> modules )
    {
        HashMap<String, Strategy> strategiesPerSolver = new HashMap<String, Strategy>();
        if( conditions.isEmpty() || modules.isEmpty() )
        {
            System.err.println( "WARNING: No condition specified, hence no strategy can be defined." );
            return strategiesPerSolver;
        }
        Pattern managerClassExtension = Pattern.compile( ".*public .*" + MANAGRECLASS + "[^a-zA-z]*", Pattern.COMMENTS + Pattern.DOTALL );
        String conditionsPattern = conditions.get( 0 );
        for( int i = 1; i != conditions.size(); ++i )
            conditionsPattern += "|" + conditions.get( i );
        String modulesPattern = "" + modules.get( 0 ).type();
        for( int i = 1; i != modules.size(); ++i )
            modulesPattern += "|" + modules.get( i ).type();
        Pattern strategyDefinition = Pattern.compile( "\\s*(.*(" + conditionsPattern + ").*,.*(" + modulesPattern + ").*)\\s*", Pattern.COMMENTS + Pattern.DOTALL );
        for( File f : STRATEGY_SOURCE_DIR.listFiles() )
        {
            String name = f.getName();
            if( name.endsWith( ".h" ) )
            {
                if( name.length() <= 2 )
                    continue;
                name = name.substring( 0, name.length() - 2 ); // remove .h extension
                // does the file contain a class definition extending Manager
                BufferedReader readFile = openFile( f );
                String line = "";
                while( (line = readLine( readFile )) != null && !line.contains( "class " + name ) );
                if( line == null )
                    continue;
                while( line != null && !managerClassExtension.matcher( line ).matches() )
                    line = readLine( readFile );
                closeFile( readFile );
                if( line == null )
                    continue;
                // yes, we found a Manager.
                strategiesPerSolver.put( name, new Strategy( "", false ) );
                // see if a cpp file is existing and read the strategy
                f = new File( STRATEGY_SOURCE_DIR + File.separator + name + ".cpp" );
                if( !f.exists() )
                    continue;
                // search lines of condition definition
                readFile = openFile( f );
                line = "";
                while( (line = readLine( readFile )) != null )
                {
                    String strategy = line;
                    Matcher strategyMatcher = strategyDefinition.matcher( strategy );
                    while( line != null && !strategyMatcher.matches() )
                    {
                        line = readLine( readFile );
                        strategy += line;
                        strategyMatcher = strategyDefinition.matcher( strategy );
                    }
                    if( line == null )
                        break;
                    // now, strategy contains one strategy definition (@todo: exclude several definitions in one line)
                    strategiesPerSolver.get( name ).add( new Strategy( strategyMatcher.group( 2 ), strategyMatcher.group( 3 ) ) );
                }
                if( strategiesPerSolver.get( name ).getChildCount() == 0 )
                {
                    System.err.println( "WARNING: Though " + name + " extends " + MANAGRECLASS + ", " + f + " does not define strategies." );
                    continue;
                }
                closeFile( readFile );
            }
        }
        return strategiesPerSolver;
    }

    /**
     * Write the module changes to the source according to the manual.
     *
     * In particular: <ul> <li>add/remove module entry in modules/Modules.h</li> <li>add/remove type entry in ModuleType.h</li> <li>add module -
     * module type mapping to Manager.cpp</li> <li>add/remove module condition to Formula.h and Formula.cpp</li> <li>add/remove module header and
     * source entries in src/CMakeLists.txt </li> </ul>
     *
     * @param module
     * @param add If this flag is true, the respective module is added to the source. Otherwise it is deleted.
     * @see Manual Sec. on "Implementing further modules"
     */
    public static void writeModule( Module module, boolean add ) throws Exception
    {
        // write module header and implementation file
        File header = new File( MODULES_SOURCE_DIR.getPath() + File.separator + module + ".h" );
        File source = new File( MODULES_SOURCE_DIR.getPath() + File.separator + module + ".cpp" );
        if( add )
        {
            if( header.exists() )
                throw new Exception( header + " does already exist. You need to remove it first before writing the module " + module + "." );
            if( source.exists() )
                throw new Exception( source + " does already exist. You need to remove it first before writing the module " + module + "." );
            PrintWriter writeFile = new PrintWriter( new FileWriter( header ) );
            writeFile.print( module.generateHeader() );
            writeFile.flush();
            writeFile.close();
            writeFile = new PrintWriter( new FileWriter( source ) );
            writeFile.print( module.generateImplementation() );
            writeFile.flush();
            writeFile.close();
        }
        else
        {
            if( !header.delete() )
                throw new Exception( "Header file " + header + " could not be deleted." );
            if( !source.delete() )
                throw new Exception( "Source file " + source + " could not be deleted." );
        }

        // write changes to Modules.h
        BufferedReader readFile = openFile( MODULES_SOURCE );
        String newFileContents = "";
        String line = "";
        if( add )
        {
            boolean notChangedYet = true;
            while( (line = readLine( readFile )) != null )
            { // read file until first #include found, then insert new includes, other contents just copied to a string
                if( notChangedYet && line.matches( ".*#include .*\".*Module.*h.*" ) ) // found entry point for new #include line
                {
                    newFileContents += "#include \"" + module + ".h\"\r\n";
                    notChangedYet = false;
                }
                newFileContents += line + "\r\n";
            }
        }
        else
        {
            while( (line = readLine( readFile )) != null )
                newFileContents += line + "\r\n";
            newFileContents = newFileContents.replaceAll( "#include \\s*\"" + module + "\\.h\"\\s*", "" ); // remove all occurences of module includes
        }
        closeFile( readFile );
        PrintWriter writeFile = new PrintWriter( new FileWriter( MODULES_SOURCE ) );
        writeFile.print( newFileContents );
        writeFile.flush();
        writeFile.close();

        // write module type to ModuleType.h
        readFile = openFile( MODULETYPE_SOURCE );
        newFileContents = "";
        line = "";
        if( add )
        {
            Pattern definitionStart = Pattern.compile( ".*enum .*" + MODULETYPE + ".*\\{.*", Pattern.COMMENTS + Pattern.DOTALL );
            boolean notChangedYet = true;
            while( (line = readLine( readFile )) != null )
            { // read file until first #include found, then insert new includes, other contents just copied to a string
                newFileContents += line + "\r\n";
                if( notChangedYet && definitionStart.matcher( newFileContents ).matches() )
                {
                    newFileContents += "        /// type of " + module + "\r\n        " + module.type() + ",\r\n";
                    notChangedYet = false;
                }
            }
        }
        else
        {
            while( (line = readLine( readFile )) != null )
                newFileContents += line + "\r\n";
            newFileContents = newFileContents.replaceAll( "\\s*///.*" + module + "\\s*" + module.type() + ",\\s*", "\r\n\n        " ); // remove all occurences of module type entries
        }
        closeFile( readFile );
        // write new contents to file
        writeFile = new PrintWriter( new FileWriter( MODULETYPE_SOURCE ) );
        writeFile.print( newFileContents );
        writeFile.flush();
        writeFile.close();

        // write module type mapping to Manager.cpp
        readFile = openFile( STRATEGY_IMPLEMENTATION );
        newFileContents = "";
        line = "";
        if( add )
        {
            Pattern definitionStart = Pattern.compile( ".*addModuleType(.*);.*", Pattern.COMMENTS + Pattern.DOTALL );
            boolean notChangedYet = true;
            while( (line = readLine( readFile )) != null )
            { // read file until first #include found, then insert new includes, other contents just copied to a string
                newFileContents += line + "\r\n";
                if( notChangedYet && definitionStart.matcher( newFileContents ).matches() )
                {
                    newFileContents += "        addModuleType( " + module.type() + ", new StandardModuleFactory<" + module + ">() );\r\n";
                    notChangedYet = false;
                }
            }
        }
        else
        {
            while( (line = readLine( readFile )) != null )
                newFileContents += line + "\r\n";
            newFileContents = newFileContents.replaceAll( "\\s*addModuleType\\(\\s*" + module.type() + ",\\s*new\\s*StandardModuleFactory<" + module + ">\\(\\s*\\)\\s*\\)\\s*;\\s*", "\r\n        " ); // remove all occurences of mapping entries
        }
        closeFile( readFile );
        // write new contents to file
        writeFile = new PrintWriter( new FileWriter( STRATEGY_IMPLEMENTATION ) );
        writeFile.print( newFileContents );
        writeFile.flush();
        writeFile.close();

        // write module condition to Formula.h
        readFile = openFile( CONDITIONS_SOURCE );
        newFileContents = "";
        line = "";
        if( add )
        {
            Pattern definitionStart = Pattern.compile( ".*static.*const.*Condition.*PROP_CANNOT_BE_SOLVED_BY_.*MODULE.*=.*Condition\\(.*\\).set\\(.*,.*\\);.*", Pattern.COMMENTS + Pattern.DOTALL );
            boolean notChangedYet = true;
            boolean readFirst = false;
            int definitionIDMax = 0;
            while( (line = readLine( readFile )) != null )
            { // read file until first #include found, then insert new includes, other contents just copied to a string
                if( definitionStart.matcher( line ).matches() )
                {
                    int first = line.indexOf( "set(" );
                    int last = line.indexOf( ",", first );
                    int id = Integer.parseInt( line.substring( first + 4, last ).trim() );
                    definitionIDMax = id > definitionIDMax ? id : definitionIDMax;
                    readFirst = true;
                }
                else if( notChangedYet && readFirst ) // and definitionStart does not match
                { // insert new definition
                    newFileContents += "    static const Condition PROP_CANNOT_BE_SOLVED_BY_" + module.toString().toUpperCase() + " = Condition().set( " + (definitionIDMax + 1) + ", 1 );\r\n";
                    notChangedYet = false;
                }
                newFileContents += line + "\r\n";
            }
        }
        else
        {
            while( (line = readLine( readFile )) != null )
                newFileContents += line + "\r\n";
            newFileContents = newFileContents.replaceAll( "\\s*static \\s*const \\s*Condition \\s*PROP_CANNOT_BE_SOLVED_BY_" + module.toString().toUpperCase() + "\\s*=\\s*Condition\\(\\s*\\)\\.set\\(\\s*[0-9]+\\s*,\\s*1\\s*\\)\\s*;\\s*", "\r\n" ); // remove all occurences of property entries
        }
        closeFile( readFile );
        // write new contents to file
        writeFile = new PrintWriter( new FileWriter( CONDITIONS_SOURCE ) );
        writeFile.print( newFileContents );
        writeFile.flush();
        writeFile.close();

        // write module type case to Formula.cpp into method notSolvableBy
        readFile = openFile( CONDITIONS_IMPLEMENTATION );
        newFileContents = "";
        line = "";
        if( add )
        {
            Pattern definitionStart = Pattern.compile( ".*switch(.*_moduleType.*).*\\{.*", Pattern.COMMENTS + Pattern.DOTALL );
            Pattern definition2Start = Pattern.compile( ".*void\\s+Formula::resetSolvableByModuleFlags(.*).*\\{.*", Pattern.COMMENTS + Pattern.DOTALL );
            String oldLine = "";
            boolean notChangedYet = true;
            boolean notChangedYet2 = true;
            while( (line = readLine( readFile )) != null )
            { // read file until first #include found, then insert new includes, other contents just copied to a string
                newFileContents += line + "\r\n";
                if( notChangedYet && definitionStart.matcher( oldLine + line ).matches() ) // consider two lines for the matching
                { // insert new case
                    newFileContents += "        case " + module.type() + ":\r\n        {\r\n            mPropositions |= PROP_CANNOT_BE_SOLVED_BY_" + module.toString().toUpperCase() + ";\r\n            break;\r\n        }\r\n";
                    notChangedYet = false;
                }
                else if( notChangedYet2 && definition2Start.matcher( oldLine + line ).matches() ) // consider two lines for the matching
                { // insert new case
                    newFileContents += "        mPropositions &= ~PROP_CANNOT_BE_SOLVED_BY_" + module.toString().toUpperCase() + ";\r\n";
                    notChangedYet2 = false;
                }
                oldLine = line;
            }
        }
        else
        {
            while( (line = readLine( readFile )) != null )
                newFileContents += line + "\r\n";
            newFileContents = newFileContents.replaceAll( "\\s*case\\s*" + module.type() + "\\s*:\\s*\\{\\s*mPropositions\\s*\\|=\\s*PROP_CANNOT_BE_SOLVED_BY_" + module.toString().toUpperCase() + ";\\s*break;\\s*\\}\\s*", "\r\n        " ); // remove all occurences of property entries
            newFileContents = newFileContents.replaceAll( "\\s*mPropositions\\s*&=\\s*~PROP_CANNOT_BE_SOLVED_BY_" + module.toString().toUpperCase() + "\\s*;\\s*", "\r\n        " ); // remove all occurences of property entries
        }
        closeFile( readFile );
        // write new contents to file
        writeFile = new PrintWriter( new FileWriter( CONDITIONS_IMPLEMENTATION ) );
        writeFile.print( newFileContents );
        writeFile.flush();
        writeFile.close();

        // write module header and source entry changes to src/CMakeLists.txt
        readFile = openFile( STRATEGY_BUILDFILE );
        newFileContents = "";
        line = "";
        if( add )
        {
            Pattern definitionStart = Pattern.compile( ".*set\\(\\s*lib_modules_headers.*", Pattern.COMMENTS + Pattern.DOTALL );
            Pattern definition2Start = Pattern.compile( ".*set\\(\\s*lib_modules_src.*", Pattern.COMMENTS + Pattern.DOTALL );
            String oldLine = "";
            boolean notChangedYet = true;
            boolean notChangedYet2 = true;
            while( (line = readLine( readFile )) != null )
            { // read file until first #include found, then insert new includes, other contents just copied to a string
                newFileContents += line + "\r\n";
                if( notChangedYet && definitionStart.matcher( oldLine + line ).matches() ) // consider two lines for the matching
                { // insert new case
                    newFileContents += "    modules" + File.separator + module + ".h\r\n";
                    notChangedYet = false;
                }
                else if( notChangedYet2 && definition2Start.matcher( oldLine + line ).matches() ) // consider two lines for the matching
                { // insert new case
                    newFileContents += "    modules" + File.separator + module + ".cpp\r\n";
                    notChangedYet2 = false;
                }
            }
        }
        else
        {
            while( (line = readLine( readFile )) != null )
                newFileContents += line + "\r\n";
            newFileContents = newFileContents.replaceAll( "\\s*modules" + File.separator + module + ".h\\s*", "\r\n    " ); // remove all occurences of header file entries
            newFileContents = newFileContents.replaceAll( "\\s*modules" + File.separator + module + ".cpp\\s*", "\r\n    " ); // remove all occurences of source file entries
        }
        closeFile( readFile );
        // write new contents to file
        writeFile = new PrintWriter( new FileWriter( STRATEGY_BUILDFILE ) );
        writeFile.print( newFileContents );
        writeFile.flush();
        writeFile.close();
    }

    /**
     * Write newly created solver to the source incrementally and non-destructively.
     *
     * In particular, create new files for new solvers, and keep existing files for existing solvers. Do not delete solvers.
     *
     * @param solver name of the solver
     * @param strategy
     * @param add If this flag is true, the respective solver is added to the source. Otherwise it is deleted.
     */
    public static void writeSolver( String solver, Strategy strategy, boolean add ) throws Exception
    {
        // write module header and implementation file
        File header = new File( STRATEGY_SOURCE_DIR.getPath() + File.separator + solver + ".h" );
        File source = new File( STRATEGY_SOURCE_DIR.getPath() + File.separator + solver + ".cpp" );
        if( add )
        {
            PrintWriter writeFile = new PrintWriter( new FileWriter( header ) );
            writeFile.print( strategy.generateHeader( solver ) );
            writeFile.flush();
            writeFile.close();
            writeFile = new PrintWriter( new FileWriter( source ) );
            writeFile.print( strategy.generateImplementation( solver ) );
            writeFile.flush();
            writeFile.close();

            if( header.exists() )
                System.err.println( "WARNING: " + header + " does already exist. Existing data will be overwritten." );
            if( source.exists() )
                System.err.println( "WARNING: " + source + " does already exist. Existing data will be overwritten." );
        }
        else
        {
            if( !header.delete() )
                throw new Exception( "Header file " + header + " could not be deleted." );
            if( !source.delete() )
                throw new Exception( "Source file " + source + " could not be deleted." );
        }
        // write solver header and source entry changes to src/CMakeLists.txt (first, remove existing entries, then write the new ones)
        BufferedReader readFile = openFile( STRATEGY_BUILDFILE );
        String newFileContents = "";
        String line = "";
        // in any case, clean all existing entries
        while( (line = readLine( readFile )) != null )
            newFileContents += line + "\r\n";
        newFileContents = newFileContents.replaceAll( "\\s*set\\(\\s*lib_" + solver.toLowerCase() + "_headers\\s*" + solver + "\\.h\\s*\\)\\s*", "\r\n" ); // remove all occurences of header file entries
        newFileContents = newFileContents.replaceAll( "\\s*set\\(\\s*lib_" + solver.toLowerCase() + "_src\\s*" + solver + "\\.cpp\\s*\\)\\s*", "\r\n\n" ); // remove all occurences of source file entries
        newFileContents = newFileContents.replaceAll( "\\s*\\$\\{lib_" + solver.toLowerCase() + "_headers\\s*\\}\\s*", "\r\n    " );
        newFileContents = newFileContents.replaceAll( "\\s*\\$\\{lib_" + solver.toLowerCase() + "_src\\}\\s*", "\r\n    " );
        if( add )
        {
            Pattern definitionStart = Pattern.compile( "\\s*set\\(lib_\\$\\{PROJECT_NAME\\}_SRCS\\s*", Pattern.COMMENTS + Pattern.DOTALL );
            Matcher definitionStartMatcher = definitionStart.matcher( newFileContents );
            if( definitionStartMatcher.find() )
            { // insert new solver entries
                int pos = definitionStartMatcher.end();
                newFileContents = newFileContents.substring( 0, definitionStartMatcher.start() )
                                  + "\r\n\nset( lib_" + solver.toLowerCase() + "_headers " + solver + ".h )\r\nset( lib_" + solver.toLowerCase() + "_src " + solver + ".cpp )\r\n"
                                  + newFileContents.substring( definitionStartMatcher.start(), definitionStartMatcher.end() )
                                  + "${lib_" + solver.toLowerCase() + "_headers} \r\n"
                                  + "    ${lib_" + solver.toLowerCase() + "_src}\r\n    "
                                  + newFileContents.substring( definitionStartMatcher.end() );
            }
            else
                throw new Exception( "Could not modify " + STRATEGY_BUILDFILE + ". Entry point not found." );
        }
        closeFile( readFile );
        PrintWriter writeFile = new PrintWriter( new FileWriter( STRATEGY_BUILDFILE ) );
        try
        {
            writeFile.print( newFileContents );
            writeFile.flush();
        }
        catch( Exception ex )
        {
            System.err.println( "ERROR: " + ex.getMessage() );
        }
    }

///////////////////////
// Auxiliary methods //
///////////////////////
    /**
     * Tries to open the specified file and returns the corresponding File object if successful; otherwise null.
     *
     * @param file
     * @return
     */
    private static BufferedReader openFile( File file )
    {
        BufferedReader readFile = null;
        try
        {
            readFile = new BufferedReader( new FileReader( file ) );
        }
        catch( FileNotFoundException f )
        {
            return null;
        }
        return readFile;
    }

    /**
     * Tries to close the specified Reader silently; errors are outputted on System.err.
     *
     * @param readFile
     */
    private static void closeFile( BufferedReader readFile )
    {
        if( readFile != null )
        {
            try
            {
                readFile.close();
            }
            catch( IOException e )
            {
                System.out.println( e );
            }
        }
    }

    /**
     * Reads from the given Reader until exactly one line is read, and returns the corresponding line as String.
     *
     * @param readFile
     * @return
     */
    private static String readLine( BufferedReader readFile )
    {
        String line = null;
        do
        {
//            // exclude empty lines
//            switch( line.charAt( 0 ) )
//            {
//                case (byte) '\n':
//                case (byte) '\r':
//                    continue;
//            }
            // reade line until it is null
            try
            {
                line = readFile.readLine();
            }
            catch( IOException e )
            {
                System.err.println( e );
            }
        }
        while( line != null && line.equals( System.getProperty( "line.separator" ) ) );
        return line;
    }
}
