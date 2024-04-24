#pragma once

namespace smtrat::mcsat {

    template<typename P>
    inline std::vector<carl::BasicConstraint<P>> constr_from_vc(const carl::VariableComparison<P>& vc, const carl::Assignment<typename P::RootType> assignment, bool tarski = false) {
        SMTRAT_LOG_FUNC("smtrat.mcsat.utils", vc << ", " << assignment << ", " << tarski)
		auto constraint = carl::as_constraint(vc);
		if (constraint) {
            SMTRAT_LOG_TRACE("smtrat.mcsat.utils", "Got " << constraint);
			return std::vector<carl::BasicConstraint<P>>({*constraint});
		} else if (tarski) {
            SMTRAT_LOG_TRACE("smtrat.mcsat.utils", "Apply Thom's lemma");
            auto poly = defining_polynomial(vc);
            std::vector<carl::BasicConstraint<P>> constraints;
            for (auto i = poly.degree(vc.var()); i > 0; i--) {
                carl::BasicConstraint<P> less_constr(poly, carl::Relation::LESS);
                auto less_eval = carl::evaluate(less_constr, assignment);
                assert(!indeterminate(less_eval));
                if (less_eval) {
                    constraints.emplace_back(less_constr);
                } else {
                    carl::BasicConstraint<P> greater_constr(poly, carl::Relation::GREATER);
                    auto greater_eval = carl::evaluate(greater_constr, assignment);
                    assert(!indeterminate(greater_eval));
                    if (greater_eval) {
                        constraints.emplace_back(greater_constr);
                    } else {
                        constraints.emplace_back(carl::BasicConstraint<P>(poly, carl::Relation::EQ));
                        assert(carl::evaluate(constraints.back(), assignment));
                    }
                }

                poly = carl::derivative(poly); //, vc.var());
            }
            SMTRAT_LOG_TRACE("smtrat.mcsat.utils", "Got " << constraints);
            return constraints;
        }
		return std::vector<carl::BasicConstraint<P>>();
	}

}