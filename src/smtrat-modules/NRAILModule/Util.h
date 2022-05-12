#pragma once

#include <carl/poly/umvpoly/Monomial.h>
#include "unordered_map"
#include <smtrat-common/smtrat-common.h>


namespace smtrat
{
    typedef std::unordered_map<carl::Variable, carl::Monomial::Arg>::iterator MonomialMapIterator;
    typedef  std::unordered_map<carl::Variable, carl::Monomial::Arg> MonomialMap;
}