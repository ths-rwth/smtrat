/**
 * @file PolyTreePool.cpp
 * @author Andreas Krueger <andreas.krueger@rwth-aachen.de>
 */

#include "PolyTreePool.h"
#include "PolyTree.h"

namespace smtrat
{
    const PolyTreeContent* PolyTreePool::get(const Poly& _poly)
    {
        auto it = mPool.find(_poly);
        if(it == mPool.end()) {
            return create(_poly);
        }
        return it->second;
    }

    const PolyTreeContent* PolyTreePool::create(const Poly& _poly)
    {
        Poly poly(_poly);
        poly.makeOrdered();

        std::size_t nrTerms = poly.nrTerms();

        if(nrTerms == 0) {
            return create(Integer(0));
        }
        if(nrTerms > 1) {
            auto lastTerm = poly.rbegin();
            return create(poly, PolyTree::Type::SUM, poly - *lastTerm, Poly(*lastTerm));
        }

        const TermT& term = poly[0];
        Rational coeff = term.coeff();

        if(term.isConstant()) {
            return create(carl::to_int<Integer>(coeff));
        }

        const carl::Monomial::Arg monomial = term.monomial();

        if(! carl::is_one(coeff)) {
            return create(poly, PolyTree::Type::PRODUCT, Poly(coeff), Poly(monomial));
        }

        auto variableAndExponent = *(monomial->begin());

        if(monomial->nrVariables() > 1) {
            carl::Monomial::Arg head = carl::MonomialPool::getInstance().create(variableAndExponent.first, variableAndExponent.second);
            carl::Monomial::Arg tail = monomial->dropVariable(variableAndExponent.first);
            return create(poly, PolyTree::Type::PRODUCT, Poly(head), Poly(tail));
        }

        if(variableAndExponent.second > 1) {
            carl::Monomial::Arg remainder = carl::MonomialPool::getInstance().create(variableAndExponent.first, variableAndExponent.second - 1);
            return create(poly, PolyTree::Type::PRODUCT, Poly(remainder), Poly(variableAndExponent.first));
        }

        return create(variableAndExponent.first);
    }

    const PolyTreeContent* PolyTreePool::create(carl::Variable::Arg _variable)
    {
        return add(new PolyTreeContent(_variable));
    }

    const PolyTreeContent* PolyTreePool::create(Integer _constant)
    {
        return add(new PolyTreeContent(_constant));
    }

    const PolyTreeContent* PolyTreePool::create(const Poly& _poly, PolyTree::Type _type, const Poly& _left, const Poly& _right)
    {
        return add(new PolyTreeContent(_poly, _type, PolyTree(_left), PolyTree(_right)));
    }

    const PolyTreeContent* PolyTreePool::add(PolyTreeContent* _element)
    {
        POOL_LOCK_GUARD

        auto insertion = mPool.insert(std::make_pair(_element->poly(), _element));
        if(! insertion.second) {
            delete _element;
        }

        return insertion.first->second;
    }
}
