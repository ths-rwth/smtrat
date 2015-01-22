/**
 * @file   RedlogTool.h
 *         Created on April 14, 2013, 6:10 PM
 * @author: Sebastian Junges
 * @author: Ulrich Loup
 * @version 2013-04-24
 *
 */

#pragma once

#include "Tool.h"

namespace benchmax {

enum RedlogMode { RLCAD, RLQE };

class RedlogTool:
    public Tool
{
    protected:
        RedlogMode mMode;

    public:
        RedlogTool(const std::string& pathToTool, RedlogMode mode);
        virtual std::string getCallToTool(const std::string& extraArguments = "") const;
        virtual BenchmarkResult getAnswer(const std::string& output) const;
        #ifdef BENCHMAX_USE_SMTPARSER
        virtual bool convertInput(Smt2Input* input);
        #endif

    private:

};

}
