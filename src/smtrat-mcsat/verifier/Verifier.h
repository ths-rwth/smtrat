#pragma once

#include <carl/core/VariablePool.h>
#include <carl/util/CheckpointVerifier.h>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace mcsat {
namespace verifier {
	inline auto getVar(const std::string& s) {
		return carl::VariablePool::getInstance().findVariableWithName(s);
	}
}
}
}

#if true
namespace smtrat {
namespace mcsat {
void initializeVerifier() {}
void clearVerifier() {}
}
}
#else
#include "Sample1.h"
#endif
