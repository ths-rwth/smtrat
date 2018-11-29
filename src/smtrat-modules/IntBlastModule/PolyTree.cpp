/**
 * @file PolyTree.cpp
 * @author Andreas Krueger <andreas.krueger@rwth-aachen.de>
 */

#include "PolyTreePool.h"
#include "PolyTree.h"

namespace smtrat
{
    PolyTree::PolyTree(const Poly& _poly) :
    mpContent(PolyTreePool::getInstance().get(_poly))
    { }

    const PolyTree& PolyTree::left() const {
        assert(mpContent->mLeft);
        return *(mpContent->mLeft);
    }

    const PolyTree& PolyTree::right() const {
        assert(mpContent->mRight);
        return *(mpContent->mRight);
    }

    carl::Variable::Arg PolyTree::variable() const {
        assert(mpContent->mType == Type::VARIABLE);
        return mpContent->mVariable;
    }

    const Integer& PolyTree::constant() const {
        assert(mpContent->mType == Type::CONSTANT);
        return mpContent->mConstant;
    }

    PolyTree::Type PolyTree::type() const {
        return mpContent->mType;
    }

    const Poly& PolyTree::poly() const {
        return mpContent->mPoly;
    }
} // namespace smtrat
