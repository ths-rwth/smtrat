#include "Bookkeeping.h"

#include <carl-arith/constraint/Conversion.h>
#include <carl-arith/extended/Conversion.h>

namespace smtrat::mcsat {

const Bookkeeping::LPAtom& Bookkeeping::lp_get(const FormulaT& f) const {
    auto iter = m_lp_map.find(f);
    if (iter == m_lp_map.end()) {
        if (f.type() == carl::FormulaType::CONSTRAINT) {
            auto vars = carl::variables(f.constraint().constr());
            auto varorder = vars.as_vector();
            carl::LPContext ctx(varorder);
            iter = m_lp_map.emplace(f, carl::convert<carl::LPPolynomial>(ctx, f.constraint().constr())).first;
        } else if (f.type() == carl::FormulaType::VARCOMPARE) {
            auto vars = carl::variables(f.variable_comparison());
            vars.erase(f.variable_comparison().var());
            auto varorder = vars.as_vector();
            varorder.push_back(f.variable_comparison().var());
            carl::LPContext ctx(varorder);
            iter = m_lp_map.emplace(f, carl::convert<carl::LPPolynomial>(ctx, f.variable_comparison())).first;
        } else {
            assert(false);
        }
    }
    return iter->second;
}


carl::ModelValue<Rational,Poly> Bookkeeping::lp_evaluate(const FormulaT& f, const carl::carlVariables& restr) const {
    if (f.type() == carl::FormulaType::CONSTRAINT || f.type() == carl::FormulaType::VARCOMPARE) {
        carl::Assignment<carl::LPPolynomial::RootType> ass;
        for (const auto& v : restr) {
            if (m_lp_ass.find(v) != m_lp_ass.end())
                ass.emplace(v, m_lp_ass.at(v));
        }

        const auto& atom = lp_get(f);
        auto res = std::holds_alternative<LPConstraint>(atom) ? carl::evaluate(std::get<LPConstraint>(atom), ass) : carl::evaluate(std::get<LPVarComp>(atom), ass);

        if (!boost::indeterminate(res)) {
            return carl::ModelValue<Rational,Poly>((bool)res);
		} else {
            return carl::createSubstitution<Rational,Poly,carl::ModelFormulaSubstitution<Rational,Poly>>(f);
        }
    } else {
        assert(false);
        return carl::createSubstitution<Rational,Poly,carl::ModelFormulaSubstitution<Rational,Poly>>(f);
    }
}

carl::ModelValue<Rational,Poly> Bookkeeping::lp_evaluate(const FormulaT& f) const {
    if (f.type() == carl::FormulaType::CONSTRAINT || f.type() == carl::FormulaType::VARCOMPARE) {
        const auto& atom = lp_get(f);
        auto res = std::holds_alternative<LPConstraint>(atom) ? carl::evaluate(std::get<LPConstraint>(atom), m_lp_ass) : carl::evaluate(std::get<LPVarComp>(atom), m_lp_ass, true);

        if (!boost::indeterminate(res)) {
            return carl::ModelValue<Rational,Poly>((bool)res);
		} else {
            return carl::createSubstitution<Rational,Poly,carl::ModelFormulaSubstitution<Rational,Poly>>(f);
        }
    } else {
        assert(false);
        // return carl::evaluate(f,mModel);
        return carl::createSubstitution<Rational,Poly,carl::ModelFormulaSubstitution<Rational,Poly>>(f);
    }
}

}