import java.util.ArrayList;
import java.util.Arrays;

/**
 * @file AllowedConditionValue.java
 *
 * @author  Henrik Schmitz
 * @since   2012-11-12
 * @version 2012-11-20
 */
public class AllowedConditionValue
{
    private static final ArrayList<String> allowedBracketValues = new ArrayList<>( Arrays.asList( new String[] { "(", ")" } ) );
    private static final ArrayList<String> allowedLogicalOperatorValues = new ArrayList<>( Arrays.asList( new String[] { "\u2227", "\u2194", "\u21d2", "\u00ac", "\u2228", "\u2295" } ) );
    private static final ArrayList<String> allowedLogicalOperatorValuesCPP = new ArrayList<>( Arrays.asList( new String[] { "&&", "==", "<=", "!", "||", "!=" } ) );
    private static final ArrayList<String> allowedLogicalOperatorValuesXML = new ArrayList<>( Arrays.asList( new String[] { "a", "e", "i", "n", "o", "x" } ) );
    private static final ArrayList<String> allowedPropositionValues = IOTools.propositions;
    private static final ArrayList<String> allowedWhitespaceValues = new ArrayList<>( Arrays.asList( new String[] { " ", "\t", "\r", "\n" } ) );
    private static final ArrayList<String> allowedWhitespaceValuesXML = new ArrayList<>( Arrays.asList( new String[] { "\\s", "\\t", "\\r", "\\n" } ) );

    private final String value;
    private final String valueCPP;
    private final String valueXML;
    private final int length;

    public AllowedConditionValue( String value )
    {
        if( allowedLogicalOperatorValues.contains( value ) )
        {
            int index = allowedLogicalOperatorValues.indexOf( value );
            this.value = value;
            valueCPP = allowedLogicalOperatorValuesCPP.get( index );
            valueXML = allowedLogicalOperatorValuesXML.get( index );
        }
        else if( allowedLogicalOperatorValuesXML.contains( value ) )
        {
            int index = allowedLogicalOperatorValuesXML.indexOf( value );
            this.value = allowedLogicalOperatorValues.get( index );
            valueCPP = allowedLogicalOperatorValuesCPP.get( index );
            valueXML = value;
        }
        else if( allowedWhitespaceValues.contains( value ) )
        {
            this.value = value;
            valueCPP = "";
            valueXML = allowedWhitespaceValuesXML.get( allowedWhitespaceValues.indexOf( value ) );
        }
        else if( allowedWhitespaceValuesXML.contains( value ) )
        {
            this.value = allowedWhitespaceValues.get( allowedWhitespaceValuesXML.indexOf( value ) );
            valueCPP = "";
            valueXML = value;
        }
        else
        {
            this.value = value;
            if( allowedBracketValues.contains( value ) )
            {
                valueCPP = value;
            }
            else
            {
                valueCPP = "PROP_" + value;
            }
            valueXML = value;
        }

        length = value.length();
    }

    public int getLength()
    {
        return length;
    }

    public String getValue()
    {
        return value;
    }

    public String getValueCPP()
    {
        return valueCPP;
    }

    public String getValueXML()
    {
        return valueXML;
    }

    public static boolean isAllowedConditionValue( String value )
    {
        return allowedBracketValues.contains( value ) || allowedLogicalOperatorValues.contains( value ) || allowedLogicalOperatorValuesXML.contains( value ) || allowedPropositionValues.contains( value ) || allowedWhitespaceValues.contains( value ) || allowedWhitespaceValuesXML.contains( value );
    }

    public static boolean isAllowedPropositionValue( String value )
    {
        return allowedPropositionValues.contains( value );
    }

    public static boolean isAllowedBracketValue( String value )
    {
        return allowedBracketValues.contains( value );
    }

    public static boolean isAllowedLogicalOperatorValue( String value )
    {
        return allowedLogicalOperatorValues.contains( value );
    }
}