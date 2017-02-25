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
		std::cout << "TRIVIAL invoked: " << x++ << std::endl;
		mis.emplace_back();
		for (const auto& it: cad.getConstraints()) mis.back().emplace(it->first);
	}
	
	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::GREEDY>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		static int x;
		std::cout << "GREEDY invoked: " << x++ << std::endl;
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
		std::cout << "CLOSURE invoked: " << x++ << std::endl;
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
		std::cout << "SAT_ACTIVITY invoked: " << x++ << std::endl;
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
				std::cout << "id: " << i << "\t activity: " << FormulaT(constraints[i]->first).activity() <<
				"\t formula: " << FormulaT(constraints[i]->first) << std::endl;
		}

		std::sort(candidates.begin(), candidates.end(), [](candidate left, candidate right) {
			return left._formula.activity() < right._formula.activity();
		});
		std::cout << "Selecting:" << std::endl;
		for(auto rit = candidates.rbegin(); rit != candidates.rend(); rit++) {
			mis.back().emplace(rit->_formula);
			cg.selectConstraint(rit->_id);
			std::cout << "id: " << rit->_id << "\t activity: " << rit->_formula.activity() <<
				"\t formula: " << rit->_formula << std::endl;
			if(!cg.hasRemainingSamples()){
				break;
			}
		}
	}
}
}
