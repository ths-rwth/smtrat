#pragma once

#include "smtrat-common.h"

#include <carl/formula/model/Model.h>

namespace smtrat {

using ModelVariable = carl::ModelVariable;
using ModelValue = carl::ModelValue<Rational, Poly>;
using Model = carl::Model<Rational, Poly>;

}