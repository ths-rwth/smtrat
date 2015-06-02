#include "EQModule.h"

namespace smtrat {
	template class EQModule<EQSettings1>;
	template class EQModule<EQSettingsForPreprocessing>;

	constexpr std::size_t HashFunctions::LARGE_CONSTANTS_<sizeof(std::size_t)>::factors[];
	constexpr std::size_t HashFunctions::LARGE_CONSTANTS_<sizeof(std::size_t)>::additive[];
}
