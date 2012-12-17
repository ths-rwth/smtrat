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

/**
 * @file Module.java
 * 
 * @author  Henrik Schmitz
 * @author  Ulrich Loup
 * @since   2012-02-13
 * @version 2012-10-17
 */
public class Module implements Comparable<Module>
{
    private static final String MODULE_TYPE_PREFIX = "MT_";

    private final String name;
    private final String type;

    /**
     * Constructs a module with name = getType.
     * @param name
     */
    public Module( String name )
    {
        this( name, MODULE_TYPE_PREFIX + name );
    }
    
    /**
     * Constructs a module with name and getType.
     * @param name
     * @param type
     */
    public Module( String name, String type )
    {
        int offset = name.lastIndexOf( "Module" );
        if( offset!=-1 )
        {
            name = name.substring( 0, offset );
        }
        this.name = name;
        this.type = type;
    }
    
    @Override
    public int compareTo( Module m )
    {
        if( m.getName()==null && this.getName()==null )
        {
            return 0;
        }
        if( this.getName()==null )
        {
            return 1;
        }
        if( m.getName()==null )
        {
            return -1;
        }
        return this.getName().compareTo( m.getName() );
    }
    
    public String getName()
    {
        return name;
    }

    /**
     * This method returns the getType, which is more an internal data field. The name is returned by toString().
     * @return getType of this string
     */
    public String getType()
    {
        return type;
    }

    @Override
    public String toString()
    {
        return getName();
    }
}