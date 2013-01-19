/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2013 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
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

import java.util.ArrayList;

/**
 * @file Condition.java
 * 
 * @author  Henrik Schmitz
 * @since   2012-10-25
 * @version 2012-11-19
 */
public class Condition
{
    public static final String TRUE_CONDITION = "TRUE";
    
    private final ArrayList<AllowedConditionValue> values;
    
    public Condition()
    {
        values = new ArrayList<>();
    }
    
    public String addElement( String element )
    {
        return addElement( values.size(), element );
    }
    
    public String addElement( int index, String element )
    {
        if( element.length()==1 )
        {    
            if( AllowedConditionValue.isAllowedConditionValue( element ) )
            {
                AllowedConditionValue av = new AllowedConditionValue( element );
                values.add( index, av );
                return av.getValue();
            }
            else
            {
                return "";
            }
        }
        else if( element.length()>1 )
        {
            ArrayList<AllowedConditionValue> valuesToBeAdded = new ArrayList<>();
            StringBuilder matchingWord = new StringBuilder();
            StringBuilder ret = new StringBuilder();
            for( int i=0; i<element.length(); i++ )
            {
                String currentValue = String.valueOf( element.charAt( i ) );
                if( matchingWord.length()==0 && AllowedConditionValue.isAllowedConditionValue( currentValue ) )
                {
                    AllowedConditionValue av = new AllowedConditionValue( currentValue );
                    valuesToBeAdded.add( av );
                    ret.append( av.getValue() );
                }
                else if( AllowedConditionValue.isAllowedConditionValue( matchingWord.append( currentValue ).toString() ) )
                {
                    AllowedConditionValue av = new AllowedConditionValue( matchingWord.toString() );
                    valuesToBeAdded.add( av );
                    ret.append( av.getValue() );
                    matchingWord.setLength( 0 );
                }
            }
            if( matchingWord.length()==0 )
            {
                values.addAll( index, valuesToBeAdded );
                return ret.toString();
            }
            else
            {
                return "";
            }
        }
        else
        {
            return "";
        }  
    }

    public String addElementAtTextPosition( int textPosition, String element )
    {
        if( values.isEmpty() )
        {
            return addElement( 0, element );
        }
        else
        {
            return addElement( calculateIndexPosition( textPosition ), element );
        }
    }

    public int calculateIndexPosition( int textPosition )
    {
        int index = 0, sum = 0;
        for( ; index<values.size() && sum<textPosition; index++ )
        {
            sum += values.get( index ).getLength();
        }
        return index;
    }
    
    public int calculateTextPosition( int oldTextPosition, int currentTextPosition )
    {
        int index = 0, newTextPosition = 0;
        for( ; index<values.size() && newTextPosition<currentTextPosition; index++ )
        {
            newTextPosition += values.get( index ).getLength();
        }
        if( currentTextPosition!=newTextPosition && currentTextPosition<oldTextPosition )
        {
            newTextPosition -= values.get( index-1 ).getLength();
        }    
        return newTextPosition;
    }
    
    public int getLength( int index )
    {
        return values.get( index ).getLength();
    }
    
    public String getValue( int index )
    {
        return values.get( index ).getValue();
    }
    
    public String getValueXML( int index )
    {
        return values.get( index ).getValueXML();
    }
    
    public boolean isEmpty()
    {
        return values.isEmpty();
    }
    
    public boolean isTrueCondition()
    {
        return values.size()==1 && values.get( 0 ).getValue().equals( TRUE_CONDITION );
    }

    public void removeElement( int index )
    {
        values.remove( index );
    }
    
    public int size()
    {
        return values.size();
    }
    
    @Override
    public String toString()
    {
        StringBuilder ret = new StringBuilder();
        for( AllowedConditionValue av : values )
        {
            ret.append( av.getValue() );
        }
        return ret.toString();
    }
    
    public String toStringCPP()
    {
        StringBuilder ret = new StringBuilder();
        for( AllowedConditionValue av : values )
        {
            ret.append( av.getValueCPP() );
        }
        return ret.toString();
    }
}