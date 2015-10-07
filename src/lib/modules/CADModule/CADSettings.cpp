#include "CADSettings.h"

constexpr carl::cad::IntegerHandling smtrat::CADSettings1::integerHandling;

const bool smtrat::CADSettings1::dummy = SettingsManager::addModule("CAD1",
	"integer_handling", carl::cad::IntegerHandling::SPLIT_EARLY, smtrat::CADSettings1::integerHandling
);
