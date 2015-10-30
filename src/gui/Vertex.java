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
    private int vertexId;
    private static int idCounter = 0;

    public Vertex( Module module )
    {
        this.module = module;
        this.vertexId = Vertex.idCounter;
        ++Vertex.idCounter;
    }
    
    public Module getModule()
    {
        return module;
    }
    
    public void setModule( Module module )
    {
        this.module = module;
    }

    public String identifier()
    {
        return module.getName() + vertexId;
    }
    
    @Override
    public String toString()
    {
        return getModule().getNameAndSettingShort();
    }
}