#include "PreprocessingSettings.h"

constexpr bool smtrat::PreprocessingSettings::removeFactors;
constexpr bool smtrat::PreprocessingSettings::checkBounds;
constexpr bool smtrat::PreprocessingSettings::splitSOS;

const bool smtrat::PreprocessingSettings::dummy = SettingsManager::addModule("Preprocessing",
	"removeFactors", true, smtrat::PreprocessingSettings::removeFactors,
	"checkBounds", true, smtrat::PreprocessingSettings::checkBounds,
	"splitSOS", true, smtrat::PreprocessingSettings::splitSOS
);
