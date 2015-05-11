import java.util.ArrayList;

/**
 * @file RecursiveDescentParser.java
 * @author  Henrik Schmitz
 * @since   2012-11-08
 * @version 2012-11-19
 * 
 * Grammar in CFG
 * S ->  E  |  C  |  D  |  EBE
 * E ->  P  | (C) | (D) | (EBE) | ~E
 * B ->  ↔  |  ⊕  |  ⇒
 * C -> C∧C |  E
 * D -> D∨D |  E
 * P -> propositions
 * 
 * Grammar in CFG and LL(1) (Removed Direct and Indirect Left Recursions)
 * S  ->  ET                           (1)
 * T  ->  ε    | ∧EC1  | ∨ED1 | BE     (2) |  (3) |  (4) |  (5)
 * E  ->  P    |  (F   | ~E            (6) |  (7) |  (8)
 * F  ->  EG                           (9)
 * G  -> ∧EC2) | ∨ED2) |  )   | BE)   (10) | (11) | (12) | (13)
 * B  ->  ↔    |   ⊕   |  ⇒           (14) | (15) | (16)
 * C1 -> ∧EC1  |   ε                  (17) | (18)
 * C2 -> ∧EC2  |   ε                  (19) | (20)
 * D1 -> ∨ED1  |   ε                  (21) | (22)
 * D2 -> ∨ED2  |   ε                  (23) | (24)
 * P  -> propositions                 (25)
 * 
 * fi(S)  = { propositions, (, ~  }   fo(S)  = { ε                   }
 * fi(T)  = { ∧, ∨, ↔, ⊕, ⇒, ε    }   fo(T)  = { ε                   }
 * fi(E)  = { propositions, (, ~  }   fo(E)  = { ∧, ∨, ↔, ⊕, ⇒, ), ε }
 * fi(F)  = { propositions, (, ~  }   fo(F)  = { ∧, ∨, ↔, ⊕, ⇒, ), ε }
 * fi(G)  = { ∧, ∨, ↔, ⊕, ⇒, )    }   fo(G)  = { ∧, ∨, ↔, ⊕, ⇒, ), ε }
 * fi(B)  = { ↔, ⊕, ⇒             }   fo(B)  = { propositions, (, ~  }
 * fi(C1) = { ∧, ε                }   fo(C1) = { ε                   }
 * fi(C2) = { ∧, ε                }   fo(C2) = { )                   }
 * fi(D1) = { ∨, ε                }   fo(C1) = { ε                   }
 * fi(D1) = { ∨, ε                }   fo(C1) = { )                   }
 * fi(P)  = { propositions        }   fo(P)  = { ∧, ∨, ↔, ⊕, ⇒, ), ε }
 * 
 *  la(1) = { propositions, (, ~  }   la(14) = { ↔                   }
 * --------------------------------   la(15) = { ⊕                   }
 *  la(2) = { ε                   }   la(16) = { ⇒                   }
 *  la(3) = { ∧                   }   --------------------------------
 *  la(4) = { ∨                   }   la(17) = { ∧                   }
 *  la(5) = { ↔, ⊕, ⇒             }   la(18) = { ε                   }
 * --------------------------------   --------------------------------
 *  la(6) = { proposition         }   la(19) = { ∧                   }
 *  la(7) = { (                   }   la(20) = { )                   }
 *  la(8) = { ~                   }   --------------------------------
 * --------------------------------   la(21) = { ∨                   }
 *  la(9) = { propositions, (, ~  }   la(22) = { ε                   }
 * --------------------------------   --------------------------------
 * la(10) = { ∧                   }   la(23) = { ∨                   }
 * la(11) = { ∨                   }   la(24) = { )                   }
 * la(12) = { )                   }   --------------------------------
 * la(13) = { ↔, ⊕, ⇒             }   la(25) = { propositions        }
 * 
 */
public class RecursiveDescentParser
{
    private final static ArrayList<String> propositions = IOTools.propositions;

    private static Condition condition;
    private static int index, size;
    private static String token;
    private static boolean parsedSuccessfully;

    public static boolean parse( Condition condition )
    {
        RecursiveDescentParser.condition = condition;
        index = 0;
        size = condition.size();
        token = next();
        parsedSuccessfully = true;
        S();
        return parsedSuccessfully;
    }
    
    private static String next()
    {
        if( index==size )
        {
            return null;
        }
        else
        {   
            String value = condition.getValueXML( index++ );
            if( value.equals( "\\s" ) || value.equals( "\\t" ) || value.equals( "\\r" ) || value.equals( "\\n" ) )
            {
                return next();
            }
            else
            {
                return value;
            }
        }
    }

    // S -> ET
    private static void S()
    {
        if( token!=null && ( propositions.contains( token ) || token.equals( "(" ) || token.equals( "n" ) ) )
        {
//            System.out.println( "1" );
            E();
            T();
            if( token!=null )
            {
                parsedSuccessfully = false;
            }
        }
        else
        {
            parsedSuccessfully = false;
        }
    }

    // T -> ε | ∧EC1 | ∨ED1 | BE
    private static void T()
    {
        if( parsedSuccessfully )
        {
            if( token==null )
            {
//                System.out.println( "2" );
            }
            else if( token.equals( "a" ) )
            {
//                System.out.println( "3" );
                token = next();
                E();
                C1();
            }
            else if( token.equals( "o" ) )
            {
//                System.out.println( "4" );
                token = next();
                E();
                D1();
            }
            else if( token.equals( "e" ) || token.equals( "x" ) || token.equals( "i" ) )
            {
//                System.out.println( "5" );
                B();
                E();
            }
            else
            {
                parsedSuccessfully = false;
            }
        }
    }

    // E -> P | (F | ~E
    private static void E()
    {
        if( parsedSuccessfully )
        {
            if( token!=null && propositions.contains( token ) )
            {
//                System.out.println( "6" );
                P();
            }
            else if( token!=null && token.equals( "(" ) )
            {
//                System.out.println( "7" );
                token = next();
                F();
            }
            else if( token!=null && token.equals( "n" ) )
            {
//                System.out.println( "8" );
                token = next();
                E();
            }
            else
            {
                parsedSuccessfully = false;
            }
        }
    }

    // F -> EG
    private static void F()
    {
        if( parsedSuccessfully )
        {
            if( token!=null && ( propositions.contains( token ) || token.equals( "(" ) || token.equals( "n" ) ) )
            {
//                System.out.println( "9" );
                E();
                G();
            }
            else
            {
                parsedSuccessfully = false;
            }
        }
    }

    // G -> ∧EC2) | ∨ED2) | ) | BE)
    private static void G()
    {
        if( parsedSuccessfully )
        {
            if( token!=null && token.equals( "a" ) )
            {
//                System.out.println( "10" );
                token = next();
                E();
                C2();
                if( token!=null && token.equals( ")" ) )
                {
                    token = next();
                }
                else
                {
                    parsedSuccessfully = false;
                }
            }
            else if( token!=null && token.equals( "o" ) )
            {
//                System.out.println( "11" );
                token = next();
                E();
                D2();
                if( token!=null && token.equals( ")" ) )
                {
                    token = next();
                }
                else
                {
                    parsedSuccessfully = false;
                }
            }
            else if( token!=null && token.equals( ")" ) )
            {
//                System.out.println( "12" );
                token = next();
            }
            else if( token!=null && ( token.equals( "e" ) || token.equals( "x" ) || token.equals( "i" ) ) )
            {
//                System.out.println( "13" );
                B();
                E();
                if( token!=null && token.equals( ")" ) )
                {
                    token = next();
                }
                else
                {
                    parsedSuccessfully = false;
                }
            }
            else
            {
                parsedSuccessfully = false;
            }
        }
    }

    // B -> ↔ | ⊕ | ⇒
    private static void B()
    {
        if( parsedSuccessfully )
        {
            if( token!=null && token.equals( "e" ) )
            {
//                System.out.println( "14" );
                token = next();
            }
            else if( token!=null && token.equals( "x" ) )
            {
//                System.out.println( "15" );
                token = next();
            }
            else if( token!=null && token.equals( "i" ) )
            {
//                System.out.println( "16" );
                token = next();
            }
            else
            {
                parsedSuccessfully = false;
            }
        }
    }

    // C1 -> ∧EC1 | ε
    private static void C1()
    {
        if( parsedSuccessfully )
        {
            if( token!=null && token.equals( "a" ) )
            {
//                System.out.println( "17" );
                token = next();
                E();
                C1();
            }
            else if( token==null )
            {
//                System.out.println( "18" );
            }
            else
            {
                parsedSuccessfully = false;
            }
        }
    }
    
    // C2 -> ∧EC2 | ε
    private static void C2()
    {
        if( parsedSuccessfully )
        {
            if( token!=null && token.equals( "a" ) )
            {
//                System.out.println( "19" );
                token = next();
                E();
                C2();
            }
            else if( token!=null && token.equals( ")" ) )
            {
//                System.out.println( "20" );
            }
            else
            {
                parsedSuccessfully = false;
            }
        }
    }

    // D1 -> ∨ED1 | ε
    private static void D1()
    {
        if( parsedSuccessfully )
        {
            if( token!=null && token.equals( "o" ) )
            {
//                System.out.println( "21" );
                token = next();
                E();
                D1();
            }
            else if( token==null )
            {
//                System.out.println( "22" );
            }
            else
            {
                parsedSuccessfully = false;
            }
        }
    }
    
    // D2 -> ∨ED2 | ε
    private static void D2()
    {
        if( parsedSuccessfully )
        {
            if( token!=null && token.equals( "o" ) )
            {
//                System.out.println( "23" );
                token = next();
                E();
                D2();
            }
            else if( token!=null && token.equals( ")" ) )
            {
//                System.out.println( "24" );
            }
            else
            {
                parsedSuccessfully = false;
            }
        }
    }

    // P -> propositions
    private static void P()
    {
        if( parsedSuccessfully )
        {
            if( token!=null && propositions.contains( token ) )
            {
//                System.out.println( "25" );
                token = next();
            }
            else
            {
                parsedSuccessfully = false;
            }
        }
    }
    
    public static class ParserException extends Exception
    {
        public static final String CONDITION_NOT_VALID = "Entered Condition is not valid. Please read the instructions for further details.";

        public ParserException( String s )
        {
            super( s );
        }
    }
}