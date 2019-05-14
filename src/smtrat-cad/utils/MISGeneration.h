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
		carl::Bitset covering;

		covering |= carl::covering::heuristic::remove_duplicates(cov.set_cover());
		SMTRAT_LOG_DEBUG("smtrat.mis", "After removing duplicates: " << covering << std::endl << cov);

		covering |= carl::covering::heuristic::select_essential(cov.set_cover());
		cov.set_cover().prune_sets();

		if (cov.set_cover().active_set_count() == 0) {
			mis.emplace_back();
			for (const auto& c: covering) {
				mis.back().emplace(cov.get_set(c));
			}
			SMTRAT_LOG_DEBUG("smtrat.mis", "returning after preconditioning");
			return;
		}
		SMTRAT_LOG_DEBUG("smtrat.mis", "After preconditioning: " << covering << std::endl << cov);

		covering |= carl::covering::heuristic::greedy_weighted(cov,
			[](const ConstraintT& c){
				constexpr double constant_weight   = 10.0;
				constexpr double complexity_weight = 0.1;
				return constant_weight + complexity_weight * c.complexity();
			}, 12
		);
		SMTRAT_LOG_DEBUG("smtrat.mis", "After greedy: " << covering << std::endl << cov);

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
				constexpr double constant_weight   = 5.0;
				constexpr double complexity_weight = 0.1;
				return constant_weight + complexity_weight * c.complexity();
			}
		);

		mis.emplace_back();
		for (const auto& c: covering) {
			mis.back().emplace(cov.get_set(c));
		}
	}
}
}
