/* 
 * File:   VariableRewriteRule.h
 * Author: Sebastian Junges
 *
 * Created on January 7, 2013
 */


#pragma once

#include "UsingDeclarations.h"


namespace smtrat{
    class VariableRewriteRule {
    public:
        VariableRewriteRule(unsigned varNr, const Term& term, const GiNaCRA::BitVector& reasons ) 
        {
            
        }

        ~VariableRewriteRule() 
        {

        }
    protected:
        /// Rewrite a variable (identified by this number)
        unsigned mVarNr;
        /// Rewrite with this term
        Term mTerm;
        /// Based on this origins
        GiNaCRA::BitVector mReasons;
    };
}


