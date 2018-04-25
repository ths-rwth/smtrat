/**
 * @file   IsatTool.h
 * @author: Sebastian Junges
 *
 *
 */

#pragma once

#include "Tool.h"

namespace benchmax {

class IsatTool: public Tool {
    public:
		IsatTool(const fs::path& binary, const std::string& arguments): Tool("iSAT", binary, arguments) {}
};

}
