#pragma once

#include "CADModule.h"

namespace smtrat {
namespace cad {
	
	template<MISHeuristic heuristic>
	class MISGeneration {
	private:
		template<typename CADModule>
		void addBoundConstraints(const CADModule& CAD, FormulaSetT& mis) const {
			FormulaSetT boundConstraints = CAD.variableBounds().getOriginSetOfBounds();
			mis.insert(boundConstraints.begin(), boundConstraints.end());
		}
	public:
		template<typename CADModule>
		void operator()(const CADModule& CAD, std::vector<FormulaSetT>& mis);
	};
	
	template<>
	template<typename CADModule>
	void MISGeneration<MISHeuristic::TRIVIAL>::operator()(const CADModule& CAD, std::vector<FormulaSetT>& mis) {
		mis.emplace_back();
		addBoundConstraints(CAD, mis.back());
		for (const auto& i: CAD.constraints()) mis.back().insert(i.first);
	}
	
	template<>
	template<typename CADModule>
	void MISGeneration<MISHeuristic::GREEDY>::operator()(const CADModule& CAD, std::vector<FormulaSetT>& mis) {
		mis.emplace_back();
		std::cout << "Starting with " << mis.back() << std::endl;
		addBoundConstraints(CAD, mis.back());
		std::cout << "Added bounds " << mis.back() << std::endl;
		auto cg = CAD.conflictGraph();
		while (cg.hasRemainingSamples()) {
			std::size_t c = cg.getMaxDegreeConstraint();
			std::cout << "Adding " << CAD.formulaFor(cg.getConstraint(c)) << " from " << cg.getConstraint(c) << std::endl;
			mis.back().insert(CAD.formulaFor(cg.getConstraint(c)));
			cg.selectConstraint(c);
		}
		std::cout << "Finally " << mis.back() << std::endl;
	}
}
}
