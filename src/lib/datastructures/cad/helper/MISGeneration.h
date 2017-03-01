#pragma once

#include "ConflictGraph.h"
#include "../Common.h"

namespace smtrat {
namespace cad {
	
	template<MISHeuristic heuristic>
	class MISGeneration {
	public:
		template<typename CAD>
		void operator()(const CAD& cad, std::vector<FormulaSetT>& mis);
	};
	
	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::TRIVIAL>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		static int x;
		SMTRAT_LOG_DEBUG("smtrat.mis", "TRIVIAL invoked: " << x++ << std::endl);
		mis.emplace_back();
		for (const auto& it: cad.getConstraints()) mis.back().emplace(it->first);
	}
	
	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::GREEDY>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		static int x;
		SMTRAT_LOG_DEBUG("smtrat.mis", "GREEDY invoked: " << x++ << std::endl);
		mis.emplace_back();
		for (const auto& c: cad.getBounds().getOriginsOfBounds()) {
			mis.back().emplace(c);
		}
		auto cg = cad.generateConflictGraph();
		while (cg.hasRemainingSamples()) {
			std::size_t c = cg.getMaxDegreeConstraint();
			mis.back().emplace(cad.getConstraints()[c]->first);
			cg.selectConstraint(c);
		}
	}

	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::CLOSURE>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		static int x;
		SMTRAT_LOG_DEBUG("smtrat.mis", "CLOSURE invoked: " << x++ << std::endl);
		mis.emplace_back();
		for (const auto& c: cad.getBounds().getOriginsOfBounds()) {
			mis.back().emplace(c);
		}
		auto cg = cad.generateConflictGraph();
		cg.disableSupersets();
		while (cg.hasRemainingSamples()) {
			std::size_t c = cg.getMaxDegreeConstraint();
			mis.back().emplace(cad.getConstraints()[c]->first);
			cg.selectConstraint(c);
		}
	}

	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::SAT_ACTIVITY>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		static int x;
		SMTRAT_LOG_DEBUG("smtrat.mis", "SAT_ACTIVITY invoked: " << x++ << std::endl);
		mis.emplace_back();
		for (const auto& c: cad.getBounds().getOriginsOfBounds()) {
			mis.back().emplace(c);
		}
		auto cg = cad.generateConflictGraph();
		auto constraints = cad.getConstraints();
		
		struct candidate {
			size_t _id;
			FormulaT _formula;
		};

		std::vector<candidate> candidates;

		for(size_t i = 0; i < constraints.size(); i++){
			candidates.emplace_back(candidate{
				i,
				FormulaT(constraints[i]->first)
			});
				SMTRAT_LOG_DEBUG("smtrat.mis", "id: " << i << "\t activity: " << FormulaT(constraints[i]->first).activity() <<
				"\t formula: " << FormulaT(constraints[i]->first) << std::endl);
		}

		std::sort(candidates.begin(), candidates.end(), [](candidate left, candidate right) {
			return left._formula.activity() < right._formula.activity();
		});
		SMTRAT_LOG_DEBUG("smtrat.mis", "Selecting:" << std::endl);
		for(auto rit = candidates.rbegin(); rit != candidates.rend(); rit++) {
			mis.back().emplace(rit->_formula);
			cg.selectConstraint(rit->_id);
			SMTRAT_LOG_DEBUG("smtrat.mis", "id: " << rit->_id << "\t activity: " << rit->_formula.activity() <<
				"\t formula: " << rit->_formula << std::endl);
			if(!cg.hasRemainingSamples()){
				break;
			}
		}
	}

	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::GREEDY_WEIGHTED>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		const static double constant_weight   = 1.0;
		const static double degree_weight     = 1.0;
		const static double complexity_weight = -0.5;
		const static double activity_weight   = 0.5;

		static int x;
		SMTRAT_LOG_DEBUG("smtrat.mis", "GREEDY_WEIGHTED invoked: " << x++ << std::endl);
		mis.emplace_back();
		for (const auto& c: cad.getBounds().getOriginsOfBounds()) {
			mis.back().emplace(c);
		}
		auto cg = cad.generateConflictGraph();
		auto constraints = cad.getConstraints();

		struct candidate {
			size_t _id;
			FormulaT _formula;
			double weight;
		};

		std::vector<candidate> candidates;
		for(size_t i = 0; i < constraints.size(); i++){
			auto constraint = constraints[i];
			auto formula = FormulaT(constraint->first);
			double weight = constant_weight +
							degree_weight * cg.getDegree(i) +
							complexity_weight * formula.complexity() +
							activity_weight * formula.activity();
			candidates.emplace_back(candidate{
				i,
				formula,
				weight
			});
			SMTRAT_LOG_DEBUG("smtrat.mis", "id: " << i << "\t weight: " << candidates.back().weight <<
			"\t formula: " << formula << std::endl);
		}

		std::sort(candidates.begin(), candidates.end(), [](candidate left, candidate right) {
			return left.weight < right.weight;
		});
		SMTRAT_LOG_DEBUG("smtrat.mis", "Selecting:" << std::endl);
		for(auto rit = candidates.rbegin(); rit != candidates.rend(); rit++) {
			mis.back().emplace(rit->_formula);
			cg.selectConstraint(rit->_id);
			SMTRAT_LOG_DEBUG("smtrat.mis", "id: " << rit->_id << "\t weight: " << rit->weight <<
				"\t formula: " << rit->_formula << std::endl);
			if(!cg.hasRemainingSamples()){
				break;
			}
		}
	}
}
}
