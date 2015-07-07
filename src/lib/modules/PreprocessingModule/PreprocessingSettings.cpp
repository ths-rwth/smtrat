#include "PreprocessingSettings.h"

CONSTEXPR bool smtrat::PreprocessingSettings::printChanges;
CONSTEXPR bool smtrat::PreprocessingSettings::removeFactors;
CONSTEXPR bool smtrat::PreprocessingSettings::eliminateMonomialEquation;
CONSTEXPR bool smtrat::PreprocessingSettings::checkBounds;
CONSTEXPR bool smtrat::PreprocessingSettings::splitSOS;
CONSTEXPR bool smtrat::PreprocessingSettings::eliminateSubstitutions;
CONSTEXPR bool smtrat::PreprocessingSettings::extractBounds;
CONSTEXPR bool smtrat::PreprocessingSettings::removeUnboundedVars;
CONSTEXPR unsigned smtrat::PreprocessingSettings::enumerate_integers_domain_size;

const bool smtrat::PreprocessingSettings::dummy = SettingsManager::addModule("Preprocessing",
	"printChanges", false, smtrat::PreprocessingSettings::printChanges,
	"eliminateMonomialEquation", true, smtrat::PreprocessingSettings::eliminateMonomialEquation,
	"removeFactors", true, smtrat::PreprocessingSettings::removeFactors,
	"checkBounds", true, smtrat::PreprocessingSettings::checkBounds,
	"splitSOS", true, smtrat::PreprocessingSettings::splitSOS,
	"eliminateSubstitutions", false, smtrat::PreprocessingSettings::eliminateSubstitutions,
	"extractBounds", true, smtrat::PreprocessingSettings::extractBounds,
	"removeUnboundedVars", true, smtrat::PreprocessingSettings::removeUnboundedVars,
    "enumerate_integers_domain_size", unsigned(0), smtrat::PreprocessingSettings::enumerate_integers_domain_size
);
