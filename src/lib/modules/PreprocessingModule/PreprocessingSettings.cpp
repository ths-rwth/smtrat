#include "PreprocessingSettings.h"

CONSTEXPR bool smtrat::PreprocessingSettings1::printChanges;
CONSTEXPR bool smtrat::PreprocessingSettings1::removeFactors;
CONSTEXPR bool smtrat::PreprocessingSettings1::eliminateMonomialEquation;
CONSTEXPR bool smtrat::PreprocessingSettings1::checkBounds;
CONSTEXPR bool smtrat::PreprocessingSettings1::splitSOS;
CONSTEXPR bool smtrat::PreprocessingSettings1::eliminateSubstitutions;
CONSTEXPR bool smtrat::PreprocessingSettings1::extractBounds;
CONSTEXPR bool smtrat::PreprocessingSettings1::removeUnboundedVars;
CONSTEXPR unsigned smtrat::PreprocessingSettings1::enumerate_integers_domain_size;

const bool smtrat::PreprocessingSettings1::dummy = SettingsManager::addModule("Preprocessing",
	"printChanges", false, smtrat::PreprocessingSettings1::printChanges,
	"eliminateMonomialEquation", true, smtrat::PreprocessingSettings1::eliminateMonomialEquation,
	"removeFactors", true, smtrat::PreprocessingSettings1::removeFactors,
	"checkBounds", true, smtrat::PreprocessingSettings1::checkBounds,
	"splitSOS", true, smtrat::PreprocessingSettings1::splitSOS,
	"eliminateSubstitutions", false, smtrat::PreprocessingSettings1::eliminateSubstitutions,
	"extractBounds", true, smtrat::PreprocessingSettings1::extractBounds,
	"removeUnboundedVars", true, smtrat::PreprocessingSettings1::removeUnboundedVars,
    "enumerate_integers_domain_size", unsigned(0), smtrat::PreprocessingSettings1::enumerate_integers_domain_size
);
