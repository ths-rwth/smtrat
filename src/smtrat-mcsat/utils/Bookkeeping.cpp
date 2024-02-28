#include "Bookkeeping.h"

#include <carl-arith/constraint/Conversion.h>

namespace smtrat::mcsat {

const carl::BasicConstraint<carl::LPPolynomial>& Bookkeeping::lp_get(const FormulaT& f) const {
    auto iter = m_lp_map.find(f);
    if (iter == m_lp_map.end()) {
        iter = m_lp_map.emplace(f, carl::convert<carl::LPPolynomial>(*m_lp_context, f.constraint().constr())).first;
    }
    return iter->second;
}


carl::ModelValue<Rational,Poly> Bookkeeping::lp_evaluate(const FormulaT& f, const carl::carlVariables& restr) const {
    if (f.type() != carl::FormulaType::CONSTRAINT) {
        return carl::evaluate(f,mModel);
    } else {
        carl::Assignment<carl::LPPolynomial::RootType> ass;
        for (const auto& v : restr) {
            if (m_lp_ass.find(v) != m_lp_ass.end())
                ass.emplace(v, m_lp_ass.at(v));
        }

        auto res = carl::evaluate(lp_get(f), ass);

        if (!boost::indeterminate(res)) {
            return carl::ModelValue<Rational,Poly>((bool)res);
		} else {
            return carl::createSubstitution<Rational,Poly,carl::ModelFormulaSubstitution<Rational,Poly>>(f);
        }
    }
}

carl::ModelValue<Rational,Poly> Bookkeeping::lp_evaluate(const FormulaT& f) const {
    if (f.type() != carl::FormulaType::CONSTRAINT) {
        return carl::evaluate(f,mModel);
    } else {
        auto res = carl::evaluate(lp_get(f), m_lp_ass);

        if (!boost::indeterminate(res)) {
            return carl::ModelValue<Rational,Poly>((bool)res);
		} else {
            return carl::createSubstitution<Rational,Poly,carl::ModelFormulaSubstitution<Rational,Poly>>(f);
        }
    }
}

}