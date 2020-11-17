#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

#include "polynomials.h"

namespace smtrat::cadcells::datastructures {

class cache { // TODO encapsulate all computations here?

    poly_pool& m_polys;

public:
    cache(poly_pool& polys) : m_polys(polys) {}

    poly_id resultant(poly_id a, poly_id b) { // TODO
        assert(a.level == b.level);
        return m_polys(carl::resultant(m_polys(a), m_polys(b)));
        
    }

    poly_id discriminant(poly_id a) { // TODO
        return m_polys(carl::discriminant(m_polys(a)));
    }

};

}