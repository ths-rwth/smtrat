#pragma once

#include "smtrat-common.h"

#include <carl/formula/model/Model.h>
#include <carl/formula/model/sqrtex/SqrtEx.h>
#include <carl/interval/Interval.h>

namespace smtrat {

using ModelVariable = carl::ModelVariable;
using ModelValue = carl::ModelValue<Rational, Poly>;
using Model = carl::Model<Rational, Poly>;

static const Model EMPTY_MODEL = Model();

using ModelSubstitution = carl::ModelSubstitution<Rational, Poly>;
using ModelPolynomialSubstitution = carl::ModelPolynomialSubstitution<Rational, Poly>;

using InfinityValue = carl::InfinityValue;

using SqrtEx = carl::SqrtEx<Poly>;

using DoubleInterval = carl::Interval<double>;
using RationalInterval = carl::Interval<Rational>;

using EvalDoubleIntervalMap = std::map<carl::Variable, DoubleInterval>;
using EvalRationalIntervalMap = std::map<carl::Variable, RationalInterval>;

}