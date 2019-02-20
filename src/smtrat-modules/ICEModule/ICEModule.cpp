/**
 * @file ICE.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-11-24
 * Created on 2015-11-24.
 */

#include "ICEModule.h"

namespace smtrat
{
	template<class Settings>
	ICEModule<Settings>::ICEModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		PModule( _formula, _conditionals, _manager )
	{}
	
	template<class Settings>
	ICEModule<Settings>::~ICEModule()
	{}
	
	template<class Settings>
	bool ICEModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		addReceivedSubformulaToPassedFormula(_subformula);
		addFormula(_subformula->formula());
		return true;
	}
	
	template<class Settings>
	void ICEModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		removeFormula(_subformula->formula());
	}
	
	template<class Settings>
	Answer ICEModule<Settings>::checkCore()
	{
		SMTRAT_LOG_DEBUG("smtrat.ice", "Obtained the following bounds: " << std::endl << mBounds);
		Answer res = processConstraints();
		if (res == UNSAT) return UNSAT;
		
		res = runBackends();
		if (res == UNSAT) getInfeasibleSubsets();
		return res;
	}
	
	template<class Settings>
	void ICEModule<Settings>::addFormula(const FormulaT& f) {
		switch (f.getType()) {
			case carl::FormulaType::CONSTRAINT:
				mBounds.addBound(f.constraint(), f);
				if (!f.constraint().isBound()) {
					mConstraints.emplace(f, f.constraint());
				}
				break;
			case carl::FormulaType::NOT: {
				if (f.subformula().getType() == carl::FormulaType::CONSTRAINT) {
					const ConstraintT& c = f.subformula().constraint();
					ConstraintT newC(c.lhs(), inverse(c.relation()));
					mBounds.addBound(newC, f);
					if (!newC.isBound()) {
						mConstraints.emplace(f, newC);
					}
				}
				break;
			}
			default:
				break;
		}
	}
	
	template<class Settings>
	void ICEModule<Settings>::removeFormula(const FormulaT& f) {
		switch (f.getType()) {
			case carl::FormulaType::CONSTRAINT:
				mBounds.removeBound(f.constraint(), f);
				if (!f.constraint().isBound()) {
					mConstraints.erase(f);
				}
				break;
			case carl::FormulaType::NOT: {
				if (f.subformula().getType() == carl::FormulaType::CONSTRAINT) {
					const ConstraintT& c = f.subformula().constraint();
					ConstraintT newC(c.lhs(), inverse(c.relation()));
					mBounds.removeBound(newC, f);
					if (!newC.isBound()) {
						mConstraints.erase(f);
					}
				}
				break;
			}
			default:
				break;
		}
	}
	
	template<class Settings>
	Answer ICEModule<Settings>::processConstraints() {
		if (mBounds.isConflicting()) {
			mInfeasibleSubsets.emplace_back(mBounds.getConflict());
			return Answer::UNSAT;
		}
		FHG graph;
		TermT src;
		std::vector<TermT> dest;
		Coefficient coeff;
		for (const auto& c: mConstraints) {
			if (isSuitable(c.second, src, dest, coeff)) {
				auto& edge = graph.newEdge(graph.newVertex(src), EdgeProperty(coeff, c.first));
				for (const auto& d: dest) {
					edge.addOut(graph.newVertex(d));
				}
			}
		}
		if (Settings::dumpAsDot) {
			SMTRAT_LOG_INFO("smtrat.ice", "Dumping resulting graph to " << Settings::dotFilename);
			graph.toDot(Settings::dotFilename);
		}

		CycleCollector collector;
		CycleEnumerator<FHG,CycleCollector> enumerator(graph, collector);
		enumerator.findAll();
		
		if (!collector.mInfeasibleSubset.empty()) {
			SMTRAT_LOG_INFO("smtrat.ice", "Found input to be unsat, subset is " << collector.mInfeasibleSubset);
			mInfeasibleSubsets.emplace_back(collector.mInfeasibleSubset);
			return UNSAT;
		}
		for (const auto& lemma: collector.mLemmas) {
			SMTRAT_LOG_DEBUG("smtrat.ice", "Adding " << lemma.first << " with origin " << lemma.second);
			addSubformulaToPassedFormula(lemma.first, lemma.second);
		}
		return SAT;
	}
	
	template<class Settings>
	bool ICEModule<Settings>::isSuitable(const ConstraintT& c, TermT& src, std::vector<TermT>& dest, Coefficient& coeff) {
		SMTRAT_LOG_FUNC("smtrat.ice", c);
		bool invert = false;
		src = TermT();
		dest.clear();
		coeff.strict = false;
		coeff.r = 0;

		switch (c.relation()) {
			case carl::Relation::EQ: break;
			case carl::Relation::NEQ: return false;
			case carl::Relation::LESS:
				invert = true;
				coeff.strict = true;
				break;
			case carl::Relation::LEQ:
				invert = true;
				break;
			case carl::Relation::GREATER:
				coeff.strict = true;
				break;
			case carl::Relation::GEQ: break;
		}
		Poly p = c.lhs();
		if (invert) p = -p;

		for (const auto& term: p) {
			if (term.isConstant()) {
				coeff.r += term.coeff();
				continue;
			}
			if (isZero(term)) {
				SMTRAT_LOG_WARN("smtrat.ice", "Term " << term << " is zero. We'll ignore it.");
				continue;
			}
			if (isSemiPositive(term)) {
				if (!carl::isZero(src)) {
					SMTRAT_LOG_TRACE("smtrat.ice", "No: Already has a source, but " << term << " was found.");
					return false;
				}
				src = term;
			} else if (isSemiNegative(term)) {
				dest.push_back(-term);
			} else {
				SMTRAT_LOG_TRACE("smtrat.ice", "No: Has indefinite term " << term << ".");
				return false;
			}
		}
		if (dest.empty()) {
			SMTRAT_LOG_TRACE("smtrat.ice", "No: No destinations were found.");
			return false;
		}
		SMTRAT_LOG_TRACE("smtrat.ice", "Yes: " << src << " -> " << dest << " with coefficient " << coeff << ".");
		return true;
	}
}

#include "Instantiation.h"
