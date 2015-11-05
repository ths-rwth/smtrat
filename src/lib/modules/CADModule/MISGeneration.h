#pragma once

#include "CADModule.h"
#include "CADSettings.h"

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
		addBoundConstraints(CAD, mis.back());
		auto cg = CAD.conflictGraph();
		while (cg.hasRemainingSamples()) {
			std::size_t c = cg.getMaxDegreeConstraint();
			mis.back().insert(CAD.formulaFor(cg.getConstraint(c)));
			cg.selectConstraint(c);
		}
	}
}
}
