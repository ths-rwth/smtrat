#include "PreprocessingSettings.h"

#ifdef __VS
const bool smtrat::PreprocessingSettings::removeFactors;
const bool smtrat::PreprocessingSettings::checkBounds;
const bool smtrat::PreprocessingSettings::splitSOS;
#else
constexpr bool smtrat::PreprocessingSettings::removeFactors;
constexpr bool smtrat::PreprocessingSettings::checkBounds;
constexpr bool smtrat::PreprocessingSettings::splitSOS;
#endif

const bool smtrat::PreprocessingSettings::dummy = SettingsManager::addModule("Preprocessing",
	"removeFactors", true, smtrat::PreprocessingSettings::removeFactors,
	"checkBounds", true, smtrat::PreprocessingSettings::checkBounds,
	"splitSOS", true, smtrat::PreprocessingSettings::splitSOS
);
