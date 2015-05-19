/**
 * @file Vertex.java
 *
 * @author  Henrik Schmitz
 * @since   2012-09-24
 * @version 2012-10-17
 */
public class Vertex
{
    private Module module;

    public Vertex( Module module )
    {
        this.module = module;
    }
    
    public Module getModule()
    {
        return module;
    }
    
    public void setModule( Module module )
    {
        this.module = module;
    }
    
    @Override
    public String toString()
    {
        return getModule().getName();
    }
}