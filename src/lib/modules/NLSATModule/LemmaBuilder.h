#pragma once

#include "../../Common.h"

#include "ExplanationGenerator.h"

#include <carl/util/Common.h>
#include <carl/util/vector_util.h>

namespace smtrat {

enum class NLSATLemmaStrategy { ORIGINAL, NEW };

namespace NLSATLemmaHelper {
	using Assignment = std::vector<std::pair<carl::Variable,FormulaT>>;
	
	inline void collectAssignments(const Assignment& assignment, FormulasT& target, const carl::Variables& vars, bool negated = false) {
		for (const auto& ass: assignment) {
			if (vars.count(ass.first) > 0) {
				target.push_back((negated ? ass.second.negated() : ass.second));
			}
		}
	}
	inline void collectAssignments(const Assignment& assignment, FormulasT& target, const FormulasT& formulas, bool negated = false) {
		carl::Variables vars;
		for (const auto& sub: formulas) sub.arithmeticVars(vars);
		collectAssignments(assignment, target, vars, negated);
	}
	inline void collectAssignments(const Assignment& assignment, FormulasT& target, const std::vector<FormulasT>& formulas, bool negated = false) {
		carl::Variables vars;
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Collecting variables from " << formulas);
		for (const auto& sub: formulas) {
			for (const auto& subsub: sub) {
				subsub.arithmeticVars(vars);
			}
		}
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Collecting assignments for " << vars);
		collectAssignments(assignment, target, vars, negated);
	}
	
	inline FormulaT buildImplication(FormulasT&& premise, const FormulaT& conclusion, bool skipNegation = false) {
		if (!skipNegation) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << premise << " -> " << conclusion);
			for (auto& p: premise) p = p.negated();
		} else {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding lemma " << premise << ", " << conclusion);
		}
		premise.push_back(conclusion);
		FormulaT res(carl::FormulaType::OR, std::move(premise));
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Clause: " << res);
		return res;
	}
}

class NLSATLemmaBuilder {
private:
	const NLSATLemmaHelper::Assignment& mAssignment;
	std::vector<FormulasT> mExplanation;
	FormulaT mConclusion;
	
	template<typename Callback>
	void generate_new_assignmentPropagation(const FormulasT& borders, const Callback& cb) {
		FormulasT base;
		NLSATLemmaHelper::collectAssignments(mAssignment, base, borders, true);
		FormulasT other = base;
		other.back() = other.back().negated();
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Generating assignment propagators");
		for (const auto& b: borders) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Propagating " << b);
			auto tmpb = base;
			auto tmpo = other;
			SMTRAT_LOG_DEBUG("smtrat.nlsat", tmpo << " -> " << b);
			cb(NLSATLemmaHelper::buildImplication(std::move(tmpo), b));
			FormulaT bneg = b.negated();
			if (b.getType() == carl::FormulaType::VARCOMPARE) {
				bneg = FormulaT(b.variableComparison().invertRelation());
			}
			SMTRAT_LOG_DEBUG("smtrat.nlsat", tmpb << " -> " << bneg);
			cb(NLSATLemmaHelper::buildImplication(std::move(tmpb), bneg));
			//cb(NLSATLemmaHelper::buildImplication({b}, bneg));
			//cb(NLSATLemmaHelper::buildImplication({bneg}, b));
		}
	}
	template<typename Callback>
	void generate_new_mainPropagation(const Callback& cb) {
		cb(NLSATLemmaHelper::buildImplication(carl::vector_concat(mExplanation), mConclusion));
	}
	template<typename Callback>
	void generate_new(const Callback& cb) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Generating explanation with new strategy");
		for (const auto& expl: mExplanation) {
			if (expl.empty()) continue;
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Processing borders: " << expl);
			generate_new_assignmentPropagation(expl, cb);
		}
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Using " << mConclusion.negated() << " for R-propagation");
		FormulasT base;
		NLSATLemmaHelper::collectAssignments(mAssignment, base, mExplanation);
		cb(NLSATLemmaHelper::buildImplication(std::move(base), mConclusion));
	}
	
	template<typename Callback>
	void generate_original(const Callback& cb) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Generating explanation with original strategy");
		for (std::size_t i = 0; i < mExplanation.size() - 1; i++) {
			const auto& expl = mExplanation[i];
			if (expl.empty()) continue;
			//SMTRAT_LOG_DEBUG("smtrat.nlsat", "Implying borders: " << expl);
			//generate_new_assignmentPropagation(expl, cb);
		}
		// Explanation as detailed in the nlsat paper
		//SMTRAT_LOG_DEBUG("smtrat.nlsat", "Generating actual explanation");
		FormulasT base;
		//NLSATLemmaHelper::collectAssignments(mAssignment, base, mExplanation, true);
		//NLSATLemmaHelper::collectAssignments(mAssignment, base, { mConclusion }, true);
		//SMTRAT_LOG_DEBUG("smtrat.nlsat", "Collected assignment: " << base);
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Explanation: " << mExplanation);
		for (const auto& expl: mExplanation) {
			for (const auto& e: expl) {
				if (e.getType() == carl::FormulaType::VARCOMPARE) {
					base.emplace_back(e.variableComparison().invertRelation());
				} else {
					base.emplace_back(e.negated());
				}
			}
		}
		//carl::vector_concat(base, mExplanation);
		cb(NLSATLemmaHelper::buildImplication(std::move(base), mConclusion, true));
	}
	
public:
	NLSATLemmaBuilder(const NLSATLemmaHelper::Assignment& assignment, const FormulaT& F, const ExplanationGenerator& eg): mAssignment(assignment), mConclusion(F) {
		eg.generateExplanation(mConclusion, mExplanation);
	}

	template<typename Callback>
	void generateLemmas(const Callback& cb, NLSATLemmaStrategy strategy) {
		switch (strategy) {
			case NLSATLemmaStrategy::NEW:
				generate_new(cb);
				break;
			case NLSATLemmaStrategy::ORIGINAL:
				generate_original(cb);
				break;
		}
	}
};
	
}
