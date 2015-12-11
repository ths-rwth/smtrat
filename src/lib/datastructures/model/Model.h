#pragma once

#include "ModelVariable.h"
#include "ModelValue.h"

namespace smtrat
{
	/// Data type for a assignment assigning a variable, represented as a string, a real algebraic number, represented as a string.
	class Model : public std::map<ModelVariable,ModelValue> {};
}

#include "ModelSubstitution.h"
