#pragma once

#include "smtrat-common.h"

#include <carl-model/Model.h>
#include <carl/vs/SqrtEx.h>
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

using MultivariateRootT = carl::MultivariateRoot<Poly>;

using DoubleInterval = carl::Interval<double>;
using RationalInterval = carl::Interval<Rational>;

using EvalDoubleIntervalMap = std::map<carl::Variable, DoubleInterval>;
using EvalRationalIntervalMap = std::map<carl::Variable, RationalInterval>;

using ObjectiveValues = std::vector<std::pair<std::variant<Poly,std::string>, Model::mapped_type>>;

}