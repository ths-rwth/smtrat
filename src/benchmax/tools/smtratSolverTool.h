/**
 * @file   smtratSolverTool.h
 *         Created on April 10, 2013, 3:37 PM
 * @author: Sebastian Junges
 *
 *
 */

#pragma once

#include "../Tool.h"

namespace benchmax {

class SmtratSolverTool:
    public Tool
{
    public:
        SmtratSolverTool(const std::string& pathToTool);
        virtual std::string getCallToTool(const std::string& extraArguments = "");

    private:

};

}