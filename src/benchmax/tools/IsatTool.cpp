/**
 * @file   IsatTool.cpp
 *         Created on April 14, 2013, 6:10 PM
 * @author: Sebastian Junges
 *
 *
 */

#include "IsatTool.h"

IsatTool::IsatTool(const std::string& pathToTool):
    Tool(TI_ISAT, pathToTool, ".hys")
{}
