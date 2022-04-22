/**
 * @file PFEModule.cpp
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#include "PFEModule.h"

namespace smtrat
{
	template<class Settings>
	PFEModule<Settings>::PFEModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager ):
		PModule( _formula, _conditionals, _manager, Settings::moduleName ),
		visitor(),
		varbounds()
	{   
		removeFactorsFunction = std::bind(&PFEModule<Settings>::removeFactors, this, std::placeholders::_1);
		removeSquaresFunction = std::bind(&PFEModule<Settings>::removeSquares, this, std::placeholders::_1);
		implyDefinitenessFunction = std::bind(&PFEModule<Settings>::implyDefiniteness, this, std::placeholders::_1);
	}

	template<class Settings>
	PFEModule<Settings>::~PFEModule()
	{}
		
	template<typename Settings>
	bool PFEModule<Settings>::addCore(ModuleInput::const_iterator _subformula) {
		if (varbounds.addBound(_subformula->formula(), _subformula->formula())) {
			boundsChanged = true;
		}
		if (varbounds.isConflicting()) {
			SMTRAT_LOG_DEBUG("smtrat.pfe", "Identified direct conflict on bounds: " << varbounds.getConflict());
			mInfeasibleSubsets.push_back(varbounds.getConflict());
			return false;
		}
		return true;
	}

	template<class Settings>
	Answer PFEModule<Settings>::checkCore() {
		auto receivedFormula = firstUncheckedReceivedSubformula();
		if (boundsChanged) {
			clearPassedFormula();
			receivedFormula = rReceivedFormula().begin();
			boundsChanged = false;
		}
		while (receivedFormula != rReceivedFormula().end()) {
			if (is_minimizing() && receivedFormula->formula().variables().find(objective()) != receivedFormula->formula().variables().end()) {
				SMTRAT_LOG_DEBUG("smtrat.pfe", "Ignoring " << receivedFormula->formula() << " as it containts the objective variable " << objective());
				addReceivedSubformulaToPassedFormula(receivedFormula);
				++receivedFormula;
				continue;
			}
			if (receivedFormula->formula().isBound()) {
				addReceivedSubformulaToPassedFormula(receivedFormula);
				++receivedFormula;
				continue;
			}
			FormulaT formula = visitor.visitResult(receivedFormula->formula(), removeFactorsFunction);
			formula = visitor.visitResult(formula, removeSquaresFunction);
			//formula = visitor.visitResult(formula, implyDefinitenessFunction);
			if (receivedFormula->formula() != formula) {
				SMTRAT_LOG_DEBUG("smtrat.pfe", "Simplified " << receivedFormula->formula());
				SMTRAT_LOG_DEBUG("smtrat.pfe", "to " << formula);
				SMTRAT_LOG_DEBUG("smtrat.pfe", "due to bounds " << varbounds.getEvalIntervalMap());
			}
			
			if (formula.isFalse()) {
				mInfeasibleSubsets.clear();
				carl::carlVariables vars;
				receivedFormula->formula().gatherVariables(vars);
				FormulaSetT infeasibleSubset = varbounds.getOriginSetOfBounds(vars.as_set());
				infeasibleSubset.insert(receivedFormula->formula());
				mInfeasibleSubsets.push_back(std::move(infeasibleSubset));
				return UNSAT;
			}
			if (!formula.isTrue()) {
				if (formula == receivedFormula->formula()) {
					addReceivedSubformulaToPassedFormula(receivedFormula);
				} else {
					carl::carlVariables vars;
					receivedFormula->formula().gatherVariables(vars);
					FormulasT origins = varbounds.getOriginsOfBounds(vars.as_set());
					origins.push_back(receivedFormula->formula());
					addSubformulaToPassedFormula(formula, std::make_shared<std::vector<FormulaT>>(std::move(origins)));
				}
			}
			++receivedFormula;
		}
		generateVariableAssignments();
		SMTRAT_LOG_DEBUG("smtrat.pfe", "Simplification: " << FormulaT(rReceivedFormula()));
		SMTRAT_LOG_DEBUG("smtrat.pfe", "to " << FormulaT(rPassedFormula()));
		Answer ans = runBackends();
		if (ans == UNSAT) {
			getInfeasibleSubsets();
		}
		return ans;
	}
	
	template<typename Settings>
	void PFEModule<Settings>::removeCore(ModuleInput::const_iterator _subformula) {
		if (varbounds.removeBound(_subformula->formula(), _subformula->formula()) == 2) {
			boundsChanged = true;
		}
	}
	
	template<typename Settings>
	FormulaT PFEModule<Settings>::removeFactors(const FormulaT& formula){
		if(formula.getType() == carl::FormulaType::CONSTRAINT) {
			const auto& factors = formula.constraint().lhs_factorization();
			SMTRAT_LOG_TRACE("smtrat.pfe", "Factorization of " << formula << " = " << factors);
			std::vector<Factorization::const_iterator> Pq;
			std::vector<Factorization::const_iterator> Pr;
			carl::Relation qrel = carl::Relation::GREATER;
			for (auto it = factors.begin(); it != factors.end(); it++) {
				auto i = carl::IntervalEvaluation::evaluate(it->first, completeBounds(it->first));
				SMTRAT_LOG_TRACE("smtrat.pfe", "Considering factor " << it->first << " with bounds " << i);
				if (i.isPositive()) {
					qrel = combine(qrel, carl::Relation::GREATER, it->second);
					Pq.push_back(it);
				} else if (i.isSemiPositive()) {
					qrel = combine(qrel, carl::Relation::GEQ, it->second);
					Pq.push_back(it);
				} else if (i.isNegative()) {
					qrel = combine(qrel, carl::Relation::LESS, it->second);
					Pq.push_back(it);
				} else if (i.isSemiNegative()) {
					qrel = combine(qrel, carl::Relation::LEQ, it->second);
					Pq.push_back(it);
				} else if (i.isZero()) {
					qrel = combine(qrel, carl::Relation::EQ, it->second);
					Pq.push_back(it);
				} else {
					Pr.push_back(it);
				}
			}
			if (!Pq.empty()) {
				carl::Relation rel = formula.constraint().relation();
				assert(qrel != carl::Relation::NEQ);
				switch (qrel) {
					case carl::Relation::GREATER: return FormulaT(getPoly(Pr), rel);
					case carl::Relation::GEQ:
						switch (rel) {
							case carl::Relation::EQ: return FormulaT(carl::FormulaType::OR, {FormulaT(getPoly(Pq), carl::Relation::EQ), FormulaT(getPoly(Pr), rel)});
							case carl::Relation::NEQ: return FormulaT(carl::FormulaType::AND, {FormulaT(getPoly(Pq), carl::Relation::GREATER), FormulaT(getPoly(Pr), rel)});
							case carl::Relation::GEQ: return FormulaT(carl::FormulaType::OR, {FormulaT(getPoly(Pq), carl::Relation::EQ), FormulaT(getPoly(Pr), rel)});
							case carl::Relation::GREATER: return FormulaT(carl::FormulaType::AND, {FormulaT(getPoly(Pq), carl::Relation::GREATER), FormulaT(getPoly(Pr), rel)});
							case carl::Relation::LEQ: return FormulaT(carl::FormulaType::OR, {FormulaT(getPoly(Pq), carl::Relation::EQ), FormulaT(getPoly(Pr), rel)});
							case carl::Relation::LESS: return FormulaT(carl::FormulaType::AND, {FormulaT(getPoly(Pq), carl::Relation::GREATER), FormulaT(getPoly(Pr), rel)});
							default: return formula;
						}
					case carl::Relation::EQ: return FormulaT(Poly(0), rel);
					case carl::Relation::LEQ:
						switch (rel) {
							case carl::Relation::EQ: return FormulaT(carl::FormulaType::OR, {FormulaT(getPoly(Pq), carl::Relation::EQ), FormulaT(getPoly(Pr), rel)});
							case carl::Relation::NEQ: return FormulaT(carl::FormulaType::AND, {FormulaT(getPoly(Pq), carl::Relation::LESS), FormulaT(getPoly(Pr), rel)});
							case carl::Relation::GEQ: return FormulaT(carl::FormulaType::OR, {FormulaT(getPoly(Pq), carl::Relation::EQ), FormulaT(getPoly(Pr), carl::Relation::LEQ)});
							case carl::Relation::GREATER: return FormulaT(carl::FormulaType::AND, {FormulaT(getPoly(Pq), carl::Relation::LESS), FormulaT(getPoly(Pr), carl::Relation::LESS)});
							case carl::Relation::LEQ: return FormulaT(carl::FormulaType::OR, {FormulaT(getPoly(Pq), carl::Relation::EQ), FormulaT(getPoly(Pr), carl::Relation::GEQ)});
							case carl::Relation::LESS: return FormulaT(carl::FormulaType::AND, {FormulaT(getPoly(Pq), carl::Relation::LESS), FormulaT(getPoly(Pr), carl::Relation::GREATER)});
							default: return formula;
						}
					case carl::Relation::LESS:
						switch (rel) {
							case carl::Relation::EQ: return FormulaT(getPoly(Pr), rel);
							case carl::Relation::NEQ: return FormulaT(getPoly(Pr), rel);
							case carl::Relation::GEQ: return FormulaT(getPoly(Pr), carl::Relation::LEQ);
							case carl::Relation::GREATER: return FormulaT(getPoly(Pr), carl::Relation::LESS);
							case carl::Relation::LEQ: return FormulaT(getPoly(Pr), carl::Relation::GEQ);
							case carl::Relation::LESS: return FormulaT(getPoly(Pr), carl::Relation::GREATER);
							default: return formula;
						}
					default: return formula;
				}
			}
		}
		return formula;
	}
	
	template<typename Settings>
	FormulaT PFEModule<Settings>::removeSquaresFromStrict(const FormulaT& formula) {
		const auto& factors = formula.constraint().lhs_factorization();
		std::vector<Factorization::const_iterator> Pq;
		std::vector<Factorization::const_iterator> Pr;
		
		for (auto it = factors.begin(); it != factors.end(); ++it) {
			if (it->second % 2 == 0) {
				// This implies that this factor is (strictly) positive and essentially reduces to factor != 0
				SMTRAT_LOG_DEBUG("smtrat.pfe", "Eliminating factors " << it->first << " ^ " << it->second);
				Pq.push_back(it);
			} else {
				Pr.push_back(it);
			}
		}
		
		if (Pq.empty()) return formula;
		
		FormulasT res;
		for (const auto& q: Pq) {
			res.emplace_back(ConstraintT(q->first, carl::Relation::NEQ));
		}
		auto polyrest = std::accumulate(Pr.begin(), Pr.end(), Poly(1), [](const auto& a, const auto& b){ return a * carl::pow(b->first, b->second); });
		res.emplace_back(ConstraintT(polyrest, formula.constraint().relation()));
		return FormulaT(carl::FormulaType::AND, std::move(res));
	}
	
	template<typename Settings>
	FormulaT PFEModule<Settings>::removeSquares(const FormulaT& formula) {
		if(formula.getType() != carl::FormulaType::CONSTRAINT) return formula;
		
		carl::Relation rel = formula.constraint().relation();
		
		switch (rel) {
			case carl::Relation::GREATER:
			case carl::Relation::LESS:
				SMTRAT_LOG_TRACE("smtrat.pfe", "Eliminating squares from " << formula);
				return removeSquaresFromStrict(formula);
			case carl::Relation::EQ:
			case carl::Relation::NEQ:
			case carl::Relation::GEQ:
			case carl::Relation::LEQ:
			default:
				SMTRAT_LOG_TRACE("smtrat.pfe", "Nothing to do for " << formula);
				return formula;
		}
	}
	
	template<typename Settings>
	FormulaT PFEModule<Settings>::implyDefinitenessFromStrict(const FormulaT& formula) {
		FormulasT res;
		res.emplace_back(formula);
		for (const auto f: formula.constraint().lhs_factorization()) {
			res.emplace_back(ConstraintT(f.first, carl::Relation::NEQ));
		}
		return FormulaT(carl::FormulaType::AND, std::move(res));
	}
	
	template<typename Settings>
	FormulaT PFEModule<Settings>::implyDefiniteness(const FormulaT& formula) {
		if(formula.getType() != carl::FormulaType::CONSTRAINT) return formula;
		
		carl::Relation rel = formula.constraint().relation();
		
		switch (rel) {
			case carl::Relation::GREATER:
			case carl::Relation::LESS:
			case carl::Relation::NEQ:
				SMTRAT_LOG_TRACE("smtrat.pfe", "Imply definiteness from " << formula);
				return implyDefinitenessFromStrict(formula);
			case carl::Relation::EQ:
			case carl::Relation::GEQ:
			case carl::Relation::LEQ:
			default:
				SMTRAT_LOG_TRACE("smtrat.pfe", "Nothing to do for " << formula);
				return formula;
		}
	}
}

#include "Instantiation.h"
