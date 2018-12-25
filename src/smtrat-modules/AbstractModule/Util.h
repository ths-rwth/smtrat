#pragma once

#include <carl/util/parser/Parser.h>
#include "carl/core/Monomial.h"
#include "unordered_map"
#include "lib/Common.h"


namespace smtrat
{
    typedef std::unordered_map<carl::Variable, carl::Monomial::Arg>::iterator MonomialMapIterator;
    typedef  std::unordered_map<carl::Variable, carl::Monomial::Arg> MonomialMap;
}