#pragma once

#include "SMTRAT.h"

namespace benchmax {

/**
 * Adapts the SMTRAT solver for OPB files.
 */
class SMTRAT_OPB: public SMTRAT {
public:
	/// Adds "-opb" to instruct SMT-RAT to parse .opb files.
	SMTRAT_OPB(const fs::path& binary, const std::string& arguments): SMTRAT(binary, arguments) {
		mArguments += " -opb";
		mName = "SMTRAT-OPB";
	}

	/// Only handles .opb files.
	virtual bool canHandle(const fs::path& path) const override {
		return is_extension(path, ".opb");
	}
};

}
