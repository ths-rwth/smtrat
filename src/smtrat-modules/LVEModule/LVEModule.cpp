/**
 * @file LVE.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2019-02-20
 * Created on 2019-02-20.
 */

#include "LVEModule.h"

#include <carl/core/polynomialfunctions/Factorization.h>
#include <carl-formula/model/substitutions/ModelConditionalSubstitution.h>

#include "utils.h"

namespace smtrat
{

	template<class Settings>
	void LVEModule<Settings>::count_variables(std::map<carl::Variable, std::size_t>& count, const ConstraintT& c) const {
		carl::carlVariables vars;
		carl::variables(c, vars);
		for (auto v: vars) {
			count[v] += 1;
		}
	}

	template<class Settings>
	std::map<carl::Variable, std::size_t> LVEModule<Settings>::get_variable_counts() const {
		std::map<carl::Variable, std::size_t> counts;
		carl::FormulaVisitor<FormulaT> v;
		for (const auto& f: rReceivedFormula()) {
			v.visit(f.formula(), [&counts,this](const auto& f){
				if (f.getType() == carl::FormulaType::CONSTRAINT) {
					count_variables(counts, f.constraint());
				}
			});
		}
		return counts;
	}

	template<class Settings>
	std::vector<carl::Variable> LVEModule<Settings>::get_lone_variables() const {
		std::vector<carl::Variable> vars;
		for (const auto& c: get_variable_counts()) {
			if (c.second == 1) {
				vars.emplace_back(c.first);
			}
		}
		return vars;
	}

	template<class Settings>
	std::optional<FormulaT> LVEModule<Settings>::eliminate_variable(carl::Variable v, const ConstraintT& c) {
		auto res = eliminate_linear(v, c);
		if (res) {
#ifdef SMTRAT_DEVOPTION_Statistics
			++mStatistics.elim_linear;
#endif
			return res;
		}
		res = eliminate_from_factors(v, c);
#ifdef SMTRAT_DEVOPTION_Statistics
		if (res) {
			++mStatistics.elim_factors;
		}
#endif
		return res;
	}

	template<class Settings>
	FormulaT LVEModule<Settings>::eliminate_from_separated_weak_inequality(carl::Variable v, const Poly& with, const Poly& without, carl::Relation rel) {
		auto res = lve::get_root(v, with);
		if (res) {
			SMTRAT_LOG_DEBUG("smtrat.lve", "Satisfying equality by selecting root " << v << " = " << *res);
			mPPModel.assign(v, *res);
			return FormulaT(carl::FormulaType::TRUE);
		} else {
			SMTRAT_LOG_DEBUG("smtrat.lve", "Factor " << with << " has no real root. Set " << v << " = 0 and eliminate factor.");
			mPPModel.assign(v, 0);
			carl::Sign sgn = lve::sgn_of_invariant_poly(v, with);
			assert(sgn == carl::Sign::NEGATIVE || sgn == carl::Sign::POSITIVE);
			if (sgn == carl::Sign::NEGATIVE) {
				switch (rel) {
					case carl::Relation::EQ:	rel = carl::Relation::EQ; break;
					case carl::Relation::LEQ:	rel = carl::Relation::GEQ; break;
					case carl::Relation::GEQ:	rel = carl::Relation::LEQ; break;
					default: assert(false);
				}
				SMTRAT_LOG_DEBUG("smtrat.lve", "-> " << FormulaT(without, rel));
				return FormulaT(without, rel);
			} else if (sgn == carl::Sign::POSITIVE) {
				SMTRAT_LOG_DEBUG("smtrat.lve", "-> " << FormulaT(without, rel));
				return FormulaT(without, rel);
			} else {
				assert(false);
				return FormulaT();
			}
		}
	}

	template<class Settings>
	FormulaT LVEModule<Settings>::eliminate_from_separated_disequality(carl::Variable v, const Poly& with, const Poly& without) {
		auto val = lve::get_non_root(v, with);
		SMTRAT_LOG_DEBUG("smtrat.lve", "Remove factor " << with << " from disequality by selecting non-root " << v << " = " << val);
		mPPModel.emplace(v, val);
		return FormulaT(without, carl::Relation::NEQ);
	}

	inline carl::Sign sign_of(carl::Relation rel, bool invert) {
		switch (rel) {
			case carl::Relation::LESS:
				return invert ? carl::Sign::POSITIVE : carl::Sign::NEGATIVE;
			case carl::Relation::GREATER:
				return invert ? carl::Sign::NEGATIVE : carl::Sign::POSITIVE;
			default:
				assert(false);
				return carl::Sign::ZERO;
		}
	}

	template<class Settings>
	FormulaT LVEModule<Settings>::eliminate_from_separated_strict_inequality(carl::Variable v, const Poly& with, const Poly& without, carl::Relation rel) {
		if (without.isConstant()) {
			SMTRAT_LOG_DEBUG("smtrat.lve", "Remaining part " << without << " is constant, we choose a proper value for " << v);
			carl::Sign target = sign_of(rel, without.constantPart() < 0);
			auto val = lve::get_value_for_sgn(v, with, target);
			if (val) {
				SMTRAT_LOG_DEBUG("smtrat.lve", "Found proper value " << v << " = " << *val << " such that " << with << " " << rel << " 0");
				mPPModel.emplace(v, *val);
				return FormulaT(carl::FormulaType::TRUE);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.lve", "No value exists for " << v << " such that " << with << " " << rel << " 0");
				return FormulaT(carl::FormulaType::FALSE);
			}
		} else {
			SMTRAT_LOG_DEBUG("smtrat.lve", "Remaining part " << without << " is not constant, we construct a conditional model for " << v);
			auto posval = lve::get_value_for_sgn(v, with, carl::Sign::POSITIVE);
			auto negval = lve::get_value_for_sgn(v, with, carl::Sign::NEGATIVE);
			assert(posval || negval);
			if (!posval) {
				SMTRAT_LOG_DEBUG("smtrat.lve", "Cannot make " << with << " positive.");
				mPPModel.emplace(v, *negval);
				switch (rel) {
					case carl::Relation::LESS:		return FormulaT(without, carl::Relation::GREATER);
					case carl::Relation::GREATER:	return FormulaT(without, carl::Relation::LESS);
					default: assert(false);
				}
				return FormulaT();
			}
			if (!negval) {
				SMTRAT_LOG_DEBUG("smtrat.lve", "Cannot make " << with << " negative.");
				mPPModel.emplace(v, *posval);
				return FormulaT(without, rel);
			}
			SMTRAT_LOG_DEBUG("smtrat.lve", "Possible values for " << v << " are " << *posval << " and " << *negval);
			if (FormulaT(without, carl::Relation::LESS).isFalse()) {
				SMTRAT_LOG_DEBUG("smtrat.lve", "Cannot make " << without << " negative.");
				switch (rel) {
					case carl::Relation::LESS:		mPPModel.emplace(v, *negval); break;
					case carl::Relation::GREATER:	mPPModel.emplace(v, *posval); break;
					default: assert(false);
				}
				return FormulaT(without, carl::Relation::GREATER);
			}
			if (FormulaT(without, carl::Relation::GREATER).isFalse()) {
				SMTRAT_LOG_DEBUG("smtrat.lve", "Cannot make " << without << " positive.");
				switch (rel) {
					case carl::Relation::LESS:		mPPModel.emplace(v, *posval); break;
					case carl::Relation::GREATER:	mPPModel.emplace(v, *negval); break;
					default: assert(false);
				}
				return FormulaT(without, carl::Relation::LESS);
			}
			std::vector<std::pair<FormulaT, ModelValue>> subs;
			switch (rel) {
				case carl::Relation::LESS:
					subs.emplace_back(FormulaT(without, carl::Relation::LESS), *posval);
					subs.emplace_back(FormulaT(without, carl::Relation::GREATER), *negval);
					break;
				case carl::Relation::GREATER:
					subs.emplace_back(FormulaT(without, carl::Relation::LESS), *negval);
					subs.emplace_back(FormulaT(without, carl::Relation::GREATER), *posval);
					break;
				default: assert(false);
			}
			mPPModel.emplace(v, carl::createSubstitution<Rational,Poly,carl::ModelConditionalSubstitution<Rational,Poly>>(subs));
			SMTRAT_LOG_DEBUG("smtrat.lve", "Constructed conditional model: " << mPPModel);
			return FormulaT(without, carl::Relation::NEQ);
		}
	}

	template<class Settings>
	std::optional<FormulaT> LVEModule<Settings>::eliminate_from_separated_factors(carl::Variable v, const Poly& with, const Poly& without, carl::Relation rel) {
		SMTRAT_LOG_DEBUG("smtrat.lve", "Considering " << v << " in " << with << " and " << without << " and relation " << rel);
		if (carl::isWeak(rel)) {
			return eliminate_from_separated_weak_inequality(v, with, without, rel);
		} else if (rel == carl::Relation::NEQ) {
			return eliminate_from_separated_disequality(v, with, without);
		} else {
			assert(carl::isStrict(rel));
			return eliminate_from_separated_strict_inequality(v, with, without, rel);
		}
		return std::nullopt;
	}

	template<class Settings>
	std::optional<FormulaT> LVEModule<Settings>::eliminate_from_factors(carl::Variable v, const ConstraintT& c) {
		Poly with_v = Poly(1);
		Poly without_v = Poly(1);
		for (const auto& factor: c.lhs_factorization()) {
			carl::carlVariables vars = carl::variables(factor.first);
			if (vars == carl::carlVariables({ v })) {
				with_v *= carl::pow(factor.first, factor.second);
			} else if (std::find(vars.begin(), vars.end(), v) == vars.end()) {
				without_v *= carl::pow(factor.first, factor.second);
			} else {
				return std::nullopt;
			}
		}
		assert(!isZero(with_v) && !isZero(without_v));
		SMTRAT_LOG_DEBUG("smtrat.lve", "Separated " << c << " into " << with_v << " and " << without_v);
		return eliminate_from_separated_factors(v, with_v, without_v, c.relation());
	}
	
	template<class Settings>
	std::optional<FormulaT> LVEModule<Settings>::eliminate_linear(carl::Variable v, const ConstraintT& c) {
		assert(c.maxDegree(v) > 0);
		if (c.maxDegree(v) > 1) {
			return std::nullopt;
		}
		// Decompose a * v - b ~ 0
		carl::Relation rel = c.relation();
		auto a = c.lhs().coeff(v, 1);
		auto b = a*v - c.lhs();
		// Now consider a * v ~ b
		SMTRAT_LOG_DEBUG("smtrat.lve", "Considering " << a << " * " << v << " " << rel << " " << b);

		if (a.isConstant()) {
			if (a.constantPart() < 0) {
				switch (rel) {
					case carl::Relation::EQ:		rel = carl::Relation::EQ; break;
					case carl::Relation::NEQ:		rel = carl::Relation::NEQ; break;
					case carl::Relation::LESS:		rel = carl::Relation::GREATER; break;
					case carl::Relation::LEQ:		rel = carl::Relation::GEQ; break;
					case carl::Relation::GREATER:	rel = carl::Relation::LESS; break;
					case carl::Relation::GEQ:		rel = carl::Relation::LEQ; break;
				}
			}
			b = b / a.constantPart();
			// Now we have v ~ b
			SMTRAT_LOG_DEBUG("smtrat.lve", "Transformed to " << v << " " << rel << " " << b);
			switch (rel) {
				case carl::Relation::EQ: break;
				case carl::Relation::NEQ: b = b + Rational(1); break;
				case carl::Relation::LESS: b = b - Rational(1); break;
				case carl::Relation::LEQ: break;
				case carl::Relation::GREATER: b = b + Rational(1); break;
				case carl::Relation::GEQ: break;
			}
			SMTRAT_LOG_DEBUG("smtrat.lve", "Eliminated with " << v << " = " << b);
			mPPModel.emplace(v, carl::createSubstitution<Rational,Poly,ModelPolynomialSubstitution>(b));
			return FormulaT(carl::FormulaType::TRUE);
		}

		return std::nullopt;
	}


	template<class Settings>
	LVEModule<Settings>::LVEModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		PModule( _formula, _conditionals, _manager, SettingsType::moduleName )
	{}
	
	template<class Settings>
	LVEModule<Settings>::~LVEModule()
	{}
	
	template<class Settings>
	void LVEModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() != Answer::UNSAT )
		{
            getBackendsModel();
			SMTRAT_LOG_DEBUG("smtrat.lve", "Got model from backend: " << mModel);
			SMTRAT_LOG_DEBUG("smtrat.lve", "Merging local model: " << mPPModel);
			mModel.update(mPPModel);
		}
	}
	
	template<class Settings>
	Answer LVEModule<Settings>::checkCore()
	{
		std::vector<carl::Variable> vars = get_lone_variables();
		if (is_minimizing()) {
			SMTRAT_LOG_DEBUG("smtrat.lve", "Ignore objective variable " << objective());
			vars.erase(std::find(vars.begin(), vars.end(), objective()));
		}
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics.lone_variables = std::max(mStatistics.lone_variables, vars.size());
#endif
		for (const auto& f: rReceivedFormula()) {
			if (f.formula().getType() == carl::FormulaType::CONSTRAINT) {
				const auto& c = f.formula().constraint();
				carl::Variable target = carl::Variable::NO_VARIABLE;
				for (auto v: vars) {
					if (c.variables().has(v)) {
						target = v;
						break;
					}
				}
				if (target != carl::Variable::NO_VARIABLE) {
					auto res = eliminate_variable(target, c);
					if (res) {
						SMTRAT_LOG_DEBUG("smtrat.lve", "Elimination: " << f.formula() << " -> " << *res);
						addSubformulaToPassedFormula(*res, f.formula());
						continue;
					}
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.lve", "No elimination for " << f.formula());
			addSubformulaToPassedFormula(f.formula(), f.formula());
		}
		auto res = runBackends();
		if (res == UNSAT) getInfeasibleSubsets();
		#ifdef SMTRAT_DEVOPTION_Statistics
			mStatistics.eliminated = std::max(mStatistics.eliminated, mPPModel.size());
		#endif
		return res;
	}
}

#include "Instantiation.h"
