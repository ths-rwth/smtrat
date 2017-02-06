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
		mis.emplace_back();
		for (const auto& it: cad.getConstraints()) mis.back().emplace(it->first);
	}
	
	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::GREEDY>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		mis.emplace_back();
		for (const auto& c: cad.getBounds().getOriginsOfBounds()) {
			mis.back().emplace(c);
			std::cout << c << std::endl;
		}
		auto cg = cad.generateConflictGraph();
		std::cout << cg << std::endl;
		while (cg.hasRemainingSamples()) {
			std::size_t c = cg.getMaxDegreeConstraint();
			mis.back().emplace(cad.getConstraints()[c]->first);
			cg.selectConstraint(c);
		}
	}

	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::CLOSURE>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		puts("CLOSURE invoked.");
		mis.emplace_back();
		for (const auto& c: cad.getBounds().getOriginsOfBounds()) {
			mis.back().emplace(c);
		}
		auto cg = cad.generateConflictGraph();
		std::cout << cg << std::endl;
		cg.disableSupersets();
		std::cout << cg << std::endl;
		while (cg.hasRemainingSamples()) {
			std::size_t c = cg.getMaxDegreeConstraint();
			mis.back().emplace(cad.getConstraints()[c]->first);
			cg.selectConstraint(c);
		}
	}

	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::SAT_ACTIVITY>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		puts("SAT_ACTIVITY invoked.");
		mis.emplace_back();
		for (const auto& c: cad.getBounds().getOriginsOfBounds()) {
			mis.back().emplace(c);
		}
		auto cg = cad.generateConflictGraph();
		std::cout << cg << std::endl;
		auto constraints = cad.getConstraints();
		/*
		struct candidate {
			size_t _id;
			FormulaT _formula;
			ConstraintT _constraint;
		};

		std::vector<candidate> candidates;

		for(size_t i = 0; i < constraints.size(); i++){
			candidates.push_back(
				i,
				FormulaT(constraints[i]->first),
				constraints[i]->first);
		}

		std::sort(ids.begin(), ids.end(), [constraints](size_t left, size_t right) {
			return constraints[left] ->first.activity() <
			       constraints[right]->first.activity();
		});
		while (cg.hasRemainingSamples()) {
			mis.back().emplace(constraints[ids.back()]);
			ids.pop_back();
			cg = cad.generateConflictGraph();
		}*/
	}
}
}
