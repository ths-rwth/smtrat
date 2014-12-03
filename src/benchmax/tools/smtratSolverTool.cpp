/**
 * @file   smtratSolverTool.cpp
 *         Created on April 10, 2013, 3:37 PM
 * @author: Sebastian Junges
 *
 *
 */

#include "smtratSolverTool.h"

namespace benchmax {

SmtratSolverTool::SmtratSolverTool(const std::string& pathToTool):
    Tool(TI_SMTRAT, pathToTool, ".smt2")
{
}

std::string SmtratSolverTool::getCallToTool(const std::string& extraArguments)
{
    if(mValidationFilePath != "")
    {
        return Tool::getCallToTool(extraArguments + " --validation:log-all,path=" + mValidationFilePath);
    }
    else
    {
        return Tool::getCallToTool(extraArguments);
    }
}

//        
//        string arguments = "";
//        if( BenchmarkTool::UseStats && mTool->toolInterface() == SMTRAT )
//        {
//            arguments += " --stats:exportXml=" + BenchmarkTool::OutputDirectory + BenchmarkTool::StatsXMLFile;
//        }
//
//        if( BenchmarkTool::ValidationTool != NULL && mTool->toolInterface() == SMTRAT )
//        {
//            arguments += " --validation:log-all,path=" + assToCheckFileName;
//        }
//        arguments += mTool->arguments( ' ' );

}