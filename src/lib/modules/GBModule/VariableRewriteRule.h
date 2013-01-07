/* 
 * File:   VariableRewriteRule.h
 * Author: Sebastian Junges
 *
 * Created on January 7, 2013
 */

#ifndef VARIABLEREWRITERULE_H
#define	VARIABLEREWRITERULE_H

#include "UsingDeclarations.h"
namespace smtrat{
    class VariableRewriteRule {
    public:
        VariableRewriteRule(unsigned varNr, Term term) {
            
        }

        ~VariableRewriteRule() 
        {

        }
    protected:
        /// Rewrite a variable (identified by this number)
        unsigned mVarNr;
        /// Rewrite with this term
        Term mTerm;
    };
}

#endif	/* VARIABLEREWRITERULE_H */

