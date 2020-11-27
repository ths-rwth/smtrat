#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

#include "polynomials.h"

namespace smtrat::cadcells::datastructures {

class projections { // TODO encapsulate all computations here?
    poly_pool& m_polys;

public:
    projections(poly_pool& polys) : m_polys(polys) {}

    poly_ref resultant(poly_ref a, poly_ref b) { // TODO implement
        assert(a.level == b.level);
        return m_polys(carl::resultant(m_polys(a), m_polys(b)));
        
    }

    poly_ref discriminant(poly_ref a) { // TODO implement
        return m_polys(carl::discriminant(m_polys(a)));
    }

};

}