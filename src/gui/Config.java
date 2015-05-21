/**
 * @file Config.java
 *
 * @author  Florian Corzilius
 * @since   2015-05-12
 * @version 2015-05-12
 */
public class Config
{
    private String carlSourcePath;
    private String manualPath;

    public Config()
    {
        this.carlSourcePath = "/home/dustin/Desktop/work/carl/src";
        this.manualPath = "/home/dustin/Desktop/work/smtrat/manual/manual_smtrat-2.0.0.pdf";
    }
    
    public String getCarlSourcePath()
    {
        return this.carlSourcePath;
    }
    
    public String getManualPath()
    {
        return this.manualPath;
    }
}
