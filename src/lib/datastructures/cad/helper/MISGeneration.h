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
		//std::cout << "rows:" << cg.numConstraints() << std::endl;
		//std::cout << "columns: " << cg.numSamples() << std::endl;
		//std::cout << "trivial columns: " << cg.numTrivialColumns() << std::endl;
		//std::cout << "unique colums: " << cg.numUniqueColumns() << std::endl;
		while (cg.hasRemainingSamples()) {
			std::size_t c = cg.getMaxDegreeConstraint();
			mis.back().emplace(cad.getConstraints()[c]->first);
			cg.selectConstraint(c);
		}
	}

	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::GREEDY_PRE>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		static int x;
		SMTRAT_LOG_DEBUG("smtrat.mis", "GREEDY_PRE invoked: " << x++ << std::endl);
		mis.emplace_back();
		for (const auto& c: cad.getBounds().getOriginsOfBounds()) {
			mis.back().emplace(c);
		}
		auto cg = cad.generateConflictGraph();
		cg = cg.removeDuplicateColumns();
		
		auto essentialConstrains = cg.selectEssentialConstraints();
		for(size_t c : essentialConstrains){
			mis.back().emplace(cad.getConstraints()[c]->first);
		}
		
		while (cg.hasRemainingSamples()) {
			std::size_t c = cg.getMaxDegreeConstraint();
			mis.back().emplace(cad.getConstraints()[c]->first);
			cg.selectConstraint(c);
		}
	}
	
	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::HYBRID>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		static int x;
		SMTRAT_LOG_DEBUG("smtrat.mis", "HYBRID invoked: " << x++ << std::endl);
		mis.emplace_back();
		for (const auto& c: cad.getBounds().getOriginsOfBounds()) {
			mis.back().emplace(c);
		}
		auto cg = cad.generateConflictGraph();
		auto essentialConstrains = cg.selectEssentialConstraints();
		for(size_t c : essentialConstrains){
			mis.back().emplace(cad.getConstraints()[c]->first);
		}
		cg = cg.removeDuplicateColumns();
		if(!cg.hasRemainingSamples()){
			return;
		}
		// Apply greedy algorithm as long as more than 6 constraints remain
		while (cg.numRemainingConstraints() > 6 && cg.hasRemainingSamples()) {
			std::size_t c = cg.getMaxDegreeConstraint();
			mis.back().emplace(cad.getConstraints()[c]->first);
			cg.selectConstraint(c);
		}

		// Find the optimum solution for the remaining constraints
		auto remaining = cg.getRemainingConstraints();
		for(size_t coverSize = 0; coverSize <= remaining.size(); coverSize++){
			std::vector<bool> selection(remaining.size() - coverSize, false);
			selection.resize(remaining.size(), true);
			do {
				carl::Bitset cover(0);
				cover.resize(cg.numSamples());
				for(size_t i = 0; i < selection.size(); i++) {
					if(selection[i]){
						cover |= remaining[i].second;
					}
				}
				if (cover.count() == cover.size()){
					for(size_t i = 0; i < selection.size(); i++) {
						if(selection[i]){
							mis.back().emplace(cad.getConstraints()[remaining[i].first]->first);
						}
					}
					return;
				}
			} while(std::next_permutation(selection.begin(), selection.end()));
		}
	}

	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::GREEDY_WEIGHTED>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		const static double constant_weight   = 1.0;
		const static double complexity_weight = 0.5;
		const static double activity_weight   = 50.0;

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
			if(cad.isIdValid(i)){
				auto constraint = constraints[i];
				auto formula = FormulaT(constraint->first);
				double weight = cg.coveredSamples(i) * (
                                constant_weight + 
								complexity_weight * formula.complexity() +
								activity_weight / formula.activity());
				candidates.emplace_back(candidate{
					i,
					formula,
					weight
				});
			}
		}

		std::sort(candidates.begin(), candidates.end(), [](candidate left, candidate right) {
			return left.weight > right.weight;
		});
		SMTRAT_LOG_DEBUG("smtrat.mis", "-------------- Included: ---------------" << std::endl);
		bool in = true;
		for(auto it = candidates.begin(); it != candidates.end(); it++) {
			SMTRAT_LOG_DEBUG("smtrat.mis", 
				"id: "            << it->_id << 
				"\t weight: "     << it->weight <<
				"\t degree: "     << cg.coveredSamples(it->_id) << 
				"\t complexity: " << it->_formula.complexity() << 
				"\t activity: "   << it->_formula.activity() <<
				std::endl);
			if(in){
				mis.back().emplace(it->_formula);
				cg.selectConstraint(it->_id);
				if(!cg.hasRemainingSamples() and (it + 1) != candidates.end()){
					in = false;
					SMTRAT_LOG_DEBUG("smtrat.mis", "------------ Not included: -------------" << std::endl);
				}
			}
		}
	}
}
}
