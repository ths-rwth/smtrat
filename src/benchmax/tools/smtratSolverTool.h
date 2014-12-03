/**
 * @file   smtratSolverTool.h
 *         Created on April 10, 2013, 3:37 PM
 * @author: Sebastian Junges
 *
 *
 */

#ifndef SMTRATSOLVERTOOL_H
#define SMTRATSOLVERTOOL_H

#include "../Tool.h"

class SmtratSolverTool:
    public Tool
{
    public:
        SmtratSolverTool(const std::string& pathToTool);
        virtual std::string getCallToTool(const std::string& extraArguments = "");

    private:

};

#endif   /* SMTRATSOLVERTOOL_H */
