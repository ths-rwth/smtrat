#pragma once

#include "CADModule.h"

namespace smtrat {
namespace cad {
	enum class MISHeuristic {
		TRIVIAL, GREEDY
	};
	
	template<MISHeuristic heuristic>
	class MISGeneration {
	private:
		const CADModule& mCAD;
		void addBoundConstraints(FormulasT& mis) const {
			FormulasT boundConstraints = mCAD.variableBounds().getOriginsOfBounds();
			mis.insert(boundConstraints.begin(), boundConstraints.end());
		}
	public:
		MISGeneration(const CADModule& cad): mCAD(cad) {}
		void operator()(std::vector<FormulasT>& mis);
	};
	
	template<>
	void MISGeneration<MISHeuristic::TRIVIAL>::operator()(std::vector<FormulasT>& mis) {
		mis.push_back(FormulasT());
		addBoundConstraints(mis.back());
		for (const auto& i: mCAD.constraints()) mis.back().insert(i.first);
	}
	
	template<>
	void MISGeneration<MISHeuristic::GREEDY>::operator()(std::vector<FormulasT>& mis) {
		mis.push_back(FormulasT());
		addBoundConstraints(mis.back());
		auto cg = mCAD.conflictGraph();
		while (cg.hasRemainingSamples()) {
			std::size_t c = cg.getMaxDegreeConstraint();
			mis.back().insert(mCAD.formulaFor(cg.getConstraint(c)));
			cg.selectConstraint(c);
		}
	}
}
}
