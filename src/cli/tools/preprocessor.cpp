#include "preprocessor.h"

#include "Executor.h"
#include "../parse_input.h"

#include "../../lib/modules/FPPModule/FPPModule.h"

namespace smtrat {
namespace preprocessor {
	class PPStrategy: public Manager {
	public:
		PPStrategy(): Manager() {
			setStrategy({
				addBackend<FPPModule<FPPSettings1>>()
			});
		}
	};
}

int preprocess_file(const std::string& filename, const std::string& outfile) {
	preprocessor::PPStrategy strategy;
	auto e = smtrat::Executor<preprocessor::PPStrategy>(strategy);
	int exitCode = executeFile(filename, e);

	auto smtrepr = carl::outputSMTLIB(strategy.logic(), { strategy.getInputSimplified().second });
	if (outfile.empty()) {
		e.regular() << smtrepr;
	} else {
		std::ofstream file(outfile);
		file << smtrepr;
		file.close();
	}

	return exitCode;
}

}