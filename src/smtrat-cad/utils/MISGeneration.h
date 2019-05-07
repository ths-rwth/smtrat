#pragma once

#include "ConflictGraph.h"
#include "../common.h"

#include <carl-covering/carl-covering.h>

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
		for (const auto& it: cad.getConstraintMap()) mis.back().emplace(it.first);
	}
	
	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::GREEDY>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		auto covering = cad.generateCovering().get_cover(carl::covering::heuristic::greedy);
		mis.emplace_back();
		for (const auto& c: covering) {
			mis.back().emplace(c);
		}
	}

	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::GREEDY_PRE>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		auto covering = cad.generateCovering().get_cover([](auto& sc) {
			carl::Bitset res;
			res |= carl::covering::heuristic::remove_duplicates(sc);
			res |= carl::covering::heuristic::select_essential(sc);
			res |= carl::covering::heuristic::greedy(sc);
			return res;
		});
		mis.emplace_back();
		for (const auto& c: covering) {
			mis.back().emplace(c);
		}
	}

	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::EXACT>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		auto covering = cad.generateCovering().get_cover(carl::covering::heuristic::exact);
		mis.emplace_back();
		for (const auto& c: covering) {
			mis.back().emplace(c);
		}
	}
	
	template<>
	template<typename CAD>
	void MISGeneration<MISHeuristic::HYBRID>::operator()(const CAD& cad, std::vector<FormulaSetT>& mis) {
		auto cov = cad.generateCovering();
		auto covering = carl::covering::heuristic::select_essential(cov.set_cover());
		cov.set_cover().prune_sets();

		if (cov.set_cover().active_set_count() == 0) {
			mis.emplace_back();
			for (const auto& c: covering) {
				mis.back().emplace(cov.get_set(c));
			}
			SMTRAT_LOG_DEBUG("smtrat.mis", "returning after preconditioning");
			return;
		}

		covering |= carl::covering::heuristic::remove_duplicates(cov.set_cover());
		covering |= carl::covering::heuristic::greedy_weighted(cov,
			[](const ConstraintT& c){
				constexpr double constant_weight   = 10.0;
				constexpr double complexity_weight = 0.1;
				return constant_weight + complexity_weight * c.complexity();
			}, 12
		);
		cov.set_cover().prune_sets();
		if (cov.set_cover().active_set_count() == 0) {
			mis.emplace_back();
			for (const auto& c: covering) {
				mis.back().emplace(cov.get_set(c));
			}
			SMTRAT_LOG_DEBUG("smtrat.mis", "returning after greedy");
			return;
		}

		SMTRAT_LOG_DEBUG("smtrat.mis", "Computing exact solution for " << cov);
		covering |= carl::covering::heuristic::exact(cov.set_cover());

		assert(cov.set_cover().active_set_count() == 0);
		mis.emplace_back();
		for (const auto& c: covering) {
			mis.back().emplace(cov.get_set(c));
		}
		SMTRAT_LOG_DEBUG("smtrat.mis", "returning exact solution");
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
