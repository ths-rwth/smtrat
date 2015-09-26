#include "CADSettings.h"

constexpr smtrat::IntegerHandling smtrat::CADSettings1::integer_handling;

const bool smtrat::CADSettings1::dummy = SettingsManager::addModule("CAD1",
	"integer_handling", IntegerHandling::SPLIT_EARLY, smtrat::CADSettings1::integer_handling
);
