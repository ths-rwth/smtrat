/**
 * @file   Z3Tool.cpp
 *         Created on April 14, 2013, 6:10 PM
 * @author: Sebastian Junges
 *
 *
 */

#include "Z3Tool.h"

namespace benchmax {

Z3Tool::Z3Tool(const std::string& pathToTool):
    Tool(TI_Z3, pathToTool, ".smt2")
{}

}
