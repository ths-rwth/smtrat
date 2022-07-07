#include "Explanation.h"
#include "onecell.h"
#include <carl-formula/formula/functions/Negations.h>

namespace smtrat::mcsat::onecell {

namespace helper {

template<typename P>
struct Conversion {};

template<>
struct Conversion<Poly> {
    Conversion(const cadcells::VariableOrdering& var_order) {}
    Poly to(const Poly& p) { return p; }
    Poly from(const Poly& p) { return p; }
    Poly::RootType to(const Poly::RootType& r) { return r; }
    Poly::RootType from(const Poly::RootType& r) { return r; }
    carl::BasicConstraint<Poly> to(const carl::BasicConstraint<Poly>& c) { return c; }
    carl::BasicConstraint<Poly> from(const carl::BasicConstraint<Poly>& c) { return c; }
    carl::VariableComparison<Poly> to(const carl::VariableComparison<Poly>& c) { return c; }
    carl::VariableComparison<Poly> from(const carl::VariableComparison<Poly>& c) { return c; }
};

template<>
struct Conversion<carl::LPPolynomial> {
    carl::LPContext m_context;
    Conversion(const cadcells::VariableOrdering& var_order) : m_context(var_order) {}
    carl::LPPolynomial to(const Poly& p) { return carl::LPPolynomial(m_context); } // TODO
    Poly from(const carl::LPPolynomial& p) { return Poly(); } // TODO
    carl::LPPolynomial::RootType to(const Poly::RootType& p) { return carl::LPPolynomial::RootType(); } // TODO
    Poly::RootType from(const carl::LPPolynomial::RootType& p) { return Poly::RootType(); } // TODO
    carl::BasicConstraint<carl::LPPolynomial> to(const carl::BasicConstraint<Poly>& c) {
        return carl::BasicConstraint<carl::LPPolynomial>(to(c.lhs()), c.relation());
    }
    carl::BasicConstraint<Poly> from(const carl::BasicConstraint<carl::LPPolynomial>& c) {
        return carl::BasicConstraint<Poly>(from(c.lhs()), c.relation());
    }
    carl::VariableComparison<carl::LPPolynomial> to(const carl::VariableComparison<Poly>& c) {
        auto k = std::holds_alternative<carl::MultivariateRoot<Poly>>(c.value()) ? std::get<carl::MultivariateRoot<Poly>>(c.value()).k() : 1;
        carl::MultivariateRoot<carl::LPPolynomial> mv(to(defining_polynomial(c)), k, c.var());
        return carl::VariableComparison<carl::LPPolynomial>(c.var(), mv, c.relation());
    }
    carl::VariableComparison<Poly> from(const carl::VariableComparison<carl::LPPolynomial>& c) {
        assert(std::holds_alternative<carl::MultivariateRoot<carl::LPPolynomial>>(c.value()));
        const auto& m = std::get<carl::MultivariateRoot<carl::LPPolynomial>>(c.value());
        carl::MultivariateRoot<Poly> mv(from(m.poly()), m.k(), m.var());
        return carl::VariableComparison<Poly>(c.var(), mv, c.relation());
    }
};

}

std::optional<mcsat::Explanation>
Explanation::operator()(const mcsat::Bookkeeping& trail, carl::Variable var, const FormulasT& reason, bool) const {
    #ifdef SMTRAT_DEVOPTION_Statistics
        mStatistics.explanationCalled();
    #endif

    cadcells::VariableOrdering vars = trail.assignedVariables();
    vars.push_back(var);

    helper::Conversion<cadcells::Polynomial> conv(vars); // TODO we need to pass the context to onecell ... (introduce Context for umvpoly?)

    cadcells::Assignment ass;
    for (const auto& [key, value] : trail.model()) {
        if (value.isRAN()) {
            ass.emplace(key.asVariable(), conv.to(value.asRAN()));
        } else {
            assert(value.isRational());
            ass.emplace(key.asVariable(), cadcells::RAN(value.asRational()));
        }
        
    }

    carl::carlVariables reason_vars;
    for (const auto& r : reason) carl::variables(r,reason_vars);
    for (const auto v : reason_vars) {
        if (ass.find(v) == ass.end() && v != var) {
            SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Conflict reasons are of higher level than the current one.");
            return std::nullopt;
        }
    }

    std::vector<cadcells::Atom> constr;
    for (const auto& r : reason) {
        if (r.type() == carl::FormulaType::CONSTRAINT) {
            constr.emplace_back(conv.to(r.constraint()));
        } else if (r.type() == carl::FormulaType::VARCOMPARE) {
            constr.emplace_back(conv.to(r.variable_comparison()));
        }
    }
    SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Explain conflict " << constr << " with " << vars << " and " << ass);
    auto result = onecell(constr, vars, ass); 

    if (!result) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Could not generate explanation");
        return std::nullopt;
    }
    else {
        #ifdef SMTRAT_DEVOPTION_Statistics
            mStatistics.explanationSuccess();
        #endif
        SMTRAT_LOG_DEBUG("smtrat.mcsat.onecell", "Got unsat cell " << result << " of constraints " << constr << " wrt " << vars << " and " << ass);
        FormulasT expl;
        for (const auto& f : reason) {
            expl.push_back(f.negated());
        }
        for (const auto& f : *result) {
            if (std::holds_alternative<cadcells::Constraint>(f)) {
                expl.push_back(FormulaT(ConstraintT(conv.from(std::get<cadcells::Constraint>(f)))).negated());
            } else if (std::holds_alternative<cadcells::VariableComparison>(f)) {
                expl.push_back(FormulaT(conv.from(std::get<cadcells::VariableComparison>(f))).negated());
            } else {
                assert(false);
            }
        }
        return mcsat::Explanation(FormulaT(carl::FormulaType::OR, std::move(expl)));
    } 
}

}