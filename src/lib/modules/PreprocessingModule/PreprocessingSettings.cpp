#include "PreprocessingSettings.h"

constexpr bool smtrat::PreprocessingSettings::removeFactors;
constexpr bool smtrat::PreprocessingSettings::checkBounds;
constexpr bool smtrat::PreprocessingSettings::splitSOS;
constexpr bool smtrat::PreprocessingSettings::eliminateSubstitutions;
constexpr bool smtrat::PreprocessingSettings::extractBounds;
constexpr bool smtrat::PreprocessingSettings::removeUnboundedVars;

const bool smtrat::PreprocessingSettings::dummy = SettingsManager::addModule("Preprocessing",
	"removeFactors", true, smtrat::PreprocessingSettings::removeFactors,
	"checkBounds", true, smtrat::PreprocessingSettings::checkBounds,
	"splitSOS", true, smtrat::PreprocessingSettings::splitSOS,
	"eliminateSubstitutions", false, smtrat::PreprocessingSettings::eliminateSubstitutions,
	"extractBounds", true, smtrat::PreprocessingSettings::extractBounds,
	"removeUnboundedVars", true, smtrat::PreprocessingSettings::removeUnboundedVars
);
