#pragma once

#include "carl/core/Monomial.h"
#include "unordered_map"


namespace smtrat
{
    typedef std::unordered_map<carl::Variable, carl::Monomial::Arg>::iterator MonomialMapIterator;
    typedef  std::unordered_map<carl::Variable, carl::Monomial::Arg> MonomialMap;
}