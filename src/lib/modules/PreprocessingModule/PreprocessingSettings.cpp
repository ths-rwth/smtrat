#include "PreprocessingSettings.h"

constexpr bool smtrat::PreprocessingSettings1::printChanges;
constexpr bool smtrat::PreprocessingSettings1::removeFactors;
constexpr bool smtrat::PreprocessingSettings1::eliminateMonomialEquation;
constexpr bool smtrat::PreprocessingSettings1::checkBounds;
constexpr bool smtrat::PreprocessingSettings1::splitSOS;
constexpr bool smtrat::PreprocessingSettings1::eliminateSubstitutions;
constexpr bool smtrat::PreprocessingSettings1::extractBounds;
constexpr bool smtrat::PreprocessingSettings1::removeUnboundedVars;
constexpr unsigned smtrat::PreprocessingSettings1::enumerate_integers_domain_size;

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
