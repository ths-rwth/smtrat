/**
 * @file   Z3Tool.h
 *         Created on April 14, 2013, 6:10 PM
 * @author: Sebastian Junges
 *
 *
 */

#pragma once

#include "Tool.h"

namespace benchmax {

class Z3: public Tool {
public:
	Z3(const fs::path& binary, const std::string& arguments): Tool("Z3", binary, arguments) {}
	virtual bool canHandle(const fs::path& path) const override {
		return isExtension(path, ".smt2");
	}
};

}
