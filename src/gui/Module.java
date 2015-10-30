/**
 * @file Module.java
 * 
 * @author  Henrik Schmitz
 * @since   2012-02-13
 * @version 2012-10-17
 */

import java.util.ArrayList;

public class Module implements Comparable<Module>
{
    private final String name;
    private ArrayList<String> settings;
    private int chosenSetting;
    
    /**
     * Constructs a module with name.
     * @param name
     */
    public Module( String name )
    {
        // int offset = name.lastIndexOf( "Module" );
        // if( offset!=-1 )
        // {
        //     name = name.substring( 0, offset );
        // }
        this.name = name;
        this.settings = new ArrayList<>();
        chosenSetting = -1;
    }

    public void addSetting( String name )
    {
        if( settings.isEmpty() )
            chosenSetting = 0;
        settings.add( name );
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
    
    public String getNameAndSetting()
    {
        if( chosenSetting == -1 )
            return name;
        return name + "<" + settings.get( chosenSetting ) + ">";
    }

    public String getNameAndSettingShort()
    {
        String modulePrefix;
        if( name.contains( "Module" ) )
            modulePrefix = name.substring( 0, name.length() - 6 );
        else
            modulePrefix = name;
        if( chosenSetting == -1 )
            return modulePrefix;
        String settingName = settings.get( chosenSetting );
        settingName = settingName.substring( modulePrefix.length() + 8, settingName.length() );
        return modulePrefix + "<" + settingName + ">";
    }
    
    public String currentSetting()
    {
        if( chosenSetting == -1 )
            return null;
        return settings.get( chosenSetting );
    }

    public int changeChosenSetting( String _setting )
    {
        chosenSetting = 0;
        for( ; chosenSetting < settings.size(); ++chosenSetting )
        {
            if( settings.get(chosenSetting).equals( _setting ) )
                return chosenSetting;
        }
        // Throw an exception?
        chosenSetting = -1;
        return chosenSetting;
    }

    public ArrayList<String> getSettings()
    {
        return settings;
    }

    @Override
    public String toString()
    {
        return getName();
    }
}