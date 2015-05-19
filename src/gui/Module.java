/**
 * @file Module.java
 * 
 * @author  Henrik Schmitz
 * @since   2012-02-13
 * @version 2012-10-17
 */
public class Module implements Comparable<Module>
{
    private final String name;
    private final String type;
    
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