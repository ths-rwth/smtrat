#include "CADSettings.h"

constexpr carl::cad::IntegerHandling smtrat::CADSettingsReal::integerHandling;

const bool smtrat::CADSettingsReal::dummy = SettingsManager::addModule("CAD1",
	"integer_handling", carl::cad::IntegerHandling::SPLIT_EARLY, smtrat::CADSettingsReal::integerHandling
);
