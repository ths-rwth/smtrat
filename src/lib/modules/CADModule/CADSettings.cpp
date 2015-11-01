#include "CADSettings.h"

#ifdef __VS
	const carl::cad::IntegerHandling smtrat::CADSettings1::integerHandling;
#else
	constexpr carl::cad::IntegerHandling smtrat::CADSettings1::integerHandling;
#endif

const bool smtrat::CADSettings1::dummy = SettingsManager::addModule("CAD1",
	"integer_handling", carl::cad::IntegerHandling::SPLIT_EARLY, smtrat::CADSettings1::integerHandling
);
