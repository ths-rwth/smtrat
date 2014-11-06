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
        VariableRewriteRule(unsigned varNr, const TermT& term, const carl::BitVector& reasons ) 
		: mVarNr(varNr), mTerm(term), mReasons(reasons)
        {
            
        }

        ~VariableRewriteRule() 
        {

        }
    protected:
        /// Rewrite a variable (identified by this number)
        unsigned mVarNr;
        /// Rewrite with this term
        TermT mTerm;
        /// Based on this origins
        carl::BitVector mReasons;
    };
}


