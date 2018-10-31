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
	void MISGeneration<MISHeuristic::GREEDY_PRE>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
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
		const static double constant_weight   = 10.0;
		const static double complexity_weight = 0.1;
		const static double activity_weight   = 10.0;
		
		// The set of constraints that will be included in every MIS
		FormulaSetT misIntersection;
	
		auto cg = cad.generateConflictGraph();
		auto essentialConstrains = cg.selectEssentialConstraints();	
		for(size_t c : essentialConstrains){
			misIntersection.emplace(cad.getConstraints()[c]->first);
		}

		if(!cg.hasRemainingSamples()){
			mis.push_back(misIntersection);
			SMTRAT_LOG_DEBUG("smtrat.mis", "returning after precon.");
			return;
		}
		cg = cg.removeDuplicateColumns();
		
		auto constraints = cad.getConstraints();
		struct candidate {
			size_t constraint;
			FormulaT formula;
			double weight;
		};
		std::vector<candidate> candidates;
		for(size_t i = 0; i < constraints.size(); i++){
			if(cad.isIdValid(i)){
				auto formula = FormulaT(constraints[i]->first);
				double weight = constant_weight +
								complexity_weight * formula.complexity() +
								activity_weight / (1.0 + formula.activity());
				candidates.push_back(candidate{i, formula, weight});
			}
		}
		// Apply greedy algorithm as long as more than 12 constraints remain
		while (cg.numRemainingConstraints() > 12 && cg.hasRemainingSamples()) {
			auto selection = std::max_element(candidates.begin(), candidates.end(),
				[cg](candidate left, candidate right) {
					return cg.coveredSamples(left.constraint)/left.weight < cg.coveredSamples(right.constraint)/right.weight;
				}
			);
			misIntersection.emplace(cad.getConstraints()[selection->constraint]->first);
			cg.selectConstraint(selection->constraint);
			candidates.erase(selection);
		}
		if(!cg.hasRemainingSamples()){
			mis.push_back(misIntersection);
			SMTRAT_LOG_DEBUG("smtrat.mis", "returning after greedy.");
			return;
		}
		SMTRAT_LOG_DEBUG("smtrat.mis", cg);
		// Find the optimum solution for the remaining constraints
		auto remaining = cg.getRemainingConstraints();
		std::set<carl::Bitset> misTails;
		for(size_t coverSize = 0; coverSize <= remaining.size(); coverSize++){
			std::vector<bool> selection(remaining.size() - coverSize, false);
			selection.resize(remaining.size(), true);
			do {
				carl::Bitset selAsBitset(0);
				selAsBitset.resize(selection.size());
				for(size_t i = 0; i < selection.size(); i++){
					selAsBitset.set(i, selection[i]);
				}
				bool skip = false;
				for(auto tail : misTails){
					if(tail.is_subset_of(selAsBitset)){
						skip = true;
						break;
					}
				}
				if(skip) continue;

				carl::Bitset cover(0);
				cover.resize(cg.numSamples());
				for(size_t i = 0; i < selection.size(); i++) {
					if(selection[i]){
						cover |= remaining[i].second;
					}
				}
				if (cover.count() == cover.size()){
					carl::Bitset tail(0);
					for(size_t i = 0; i < selection.size(); i++) {
						tail.set(i, selection[i]);
					}
					misTails.insert(tail);
					SMTRAT_LOG_DEBUG("smtrat.mis", "tail found: " << selection);
				}
			} while(std::next_permutation(selection.begin(), selection.end()));
		}
		for(auto tail : misTails){
			mis.emplace_back();
			for(auto f : misIntersection){
				mis.back().insert(f);
			}
			for(size_t i = 0; i < tail.size(); i++){
				if(tail.test(i)){
					mis.back().emplace(cad.getConstraints()[remaining[i].first]->first);
				}
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.mis", "returning " << mis.size() << " MISes.");
	}

	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::GREEDY_WEIGHTED>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		const static double constant_weight   = 5.0;
		const static double complexity_weight = 0.1;
		const static double activity_weight   = 10.0;

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

		auto constraints = cad.getConstraints();
		struct candidate {
			size_t constraint;
			FormulaT formula;
			double weight;
		};

		std::vector<candidate> candidates;
		for(size_t i = 0; i < constraints.size(); i++){
			if(cad.isIdValid(i)){
				auto constraint = constraints[i];
				auto formula = FormulaT(constraint->first);
				double weight = constant_weight +
								complexity_weight * formula.complexity() +
								activity_weight / (1.0 + formula.activity());
				candidates.push_back(candidate{
					i,
					formula,
					weight
				});
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.mis", cg);
		SMTRAT_LOG_DEBUG("smtrat.mis", "-------------- Included: ---------------");
		
		while (cg.hasRemainingSamples()) {
			auto selection = std::max_element(candidates.begin(), candidates.end(),
				[cg](candidate left, candidate right) {
					return cg.coveredSamples(left.constraint)/left.weight < cg.coveredSamples(right.constraint)/right.weight;
				}
			);
			SMTRAT_LOG_DEBUG("smtrat.mis", 
				"id: "            << selection->constraint << 
				"\t weight: "     << selection->weight <<
				"\t degree: "     << cg.coveredSamples(selection->constraint) << 
				"\t complexity: " << selection->formula.complexity() << 
				"\t activity: "   << selection->formula.activity());
			mis.back().emplace(cad.getConstraints()[selection->constraint]->first);
			cg.selectConstraint(selection->constraint);
			candidates.erase(selection);
		}
		SMTRAT_LOG_DEBUG("smtrat.mis", "----------------------------------------");
	}
}
}
