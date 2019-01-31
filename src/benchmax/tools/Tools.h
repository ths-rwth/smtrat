#pragma once

#include "Tool.h"

#include <memory>
#include <vector>

namespace benchmax {

using ToolPtr = std::unique_ptr<Tool>;
using Tools = std::vector<ToolPtr>;

template<typename T>
void createTools(const std::vector<std::string>& arguments, Tools& tools);

Tools loadTools();

}
