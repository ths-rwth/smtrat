#pragma once

#include "../Common.h"

namespace smtrat {
namespace cad {

template<CoreHeuristic CH>
struct CADCore {};

template<>
struct CADCore<CoreHeuristic::BySample> {
	template<typename CAD>
	Answer operator()(Assignment& assignment, CAD& cad) {
		cad.mLifting.resetFullSamples();
		cad.mLifting.restoreRemovedSamples();
		while (true) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current sample tree:" << std::endl << cad.mLifting.getTree());
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current sample queue:" << std::endl << cad.mLifting.getLiftingQueue());
			Answer res = cad.checkFullSamples(assignment);
			if (res == Answer::SAT) return Answer::SAT;
			
			if (!cad.mLifting.hasNextSample()) {
				SMTRAT_LOG_DEBUG("smtrat.cad", "There is no sample to be lifted.");
				break;
			}
			auto it = cad.mLifting.getNextSample();
			Sample& s = *it;
			SMTRAT_LOG_DEBUG("smtrat.cad", "Sample " << s << " at depth " << it.depth());
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current sample: " << cad.mLifting.printSample(it));
			assert(0 <= it.depth() && it.depth() < cad.dim());
			if (s.hasConflictWithConstraint()) {
				SMTRAT_LOG_DEBUG("smtrat.cad", "Sample " << s << " already has a conflict.");
				cad.mLifting.removeNextSample();
				continue;
			}
			auto polyID = cad.mProjection.getPolyForLifting(cad.idLP(it.depth() + 1), s.liftedWith());
			if (polyID) {
				const auto& poly = cad.mProjection.getPolynomialById(cad.idLP(it.depth() + 1), *polyID);
				SMTRAT_LOG_DEBUG("smtrat.cad", "Lifting " << s << " with " << poly);
				cad.mLifting.liftSample(it, poly, *polyID);
			} else {
				cad.mLifting.removeNextSample();
				if (!cad.mLifting.hasNextSample()) {
					SMTRAT_LOG_DEBUG("smtrat.cad", "Got nothing to lift anymore, projecting into level " << idLP(it.depth() + 1) << " ...");
					carl::Bitset gotNewPolys = cad.mProjection.projectNewPolynomial();
					if (gotNewPolys.any()) {
						SMTRAT_LOG_TRACE("smtrat.cad", "Current projection:" << std::endl << cad.mProjection);
						cad.mLifting.restoreRemovedSamples();
					}
				}
			}
		}
		return Answer::UNSAT;
	}
};

template<>
struct CADCore<CoreHeuristic::PreferProjection> {
	template<typename CAD>
	Answer operator()(Assignment& assignment, CAD& cad) {
		cad.mLifting.resetFullSamples();
		cad.mLifting.restoreRemovedSamples();
		while (true) {
			Answer res = cad.checkFullSamples(assignment);
			if (res == Answer::SAT) return Answer::SAT;
			
			if (!cad.mLifting.hasNextSample()) {
				SMTRAT_LOG_DEBUG("smtrat.cad", "There is no sample to be lifted.");
				return Answer::UNSAT;
			}
			
			auto it = cad.mLifting.getNextSample();
			Sample& s = *it;
			assert(0 <= it.depth() && it.depth() < cad.dim());
			if (s.hasConflictWithConstraint()) {
				cad.mLifting.removeNextSample();
				continue;
			}
			
			auto polyID = cad.mProjection.getPolyForLifting(cad.idLP(it.depth() + 1), s.liftedWith());
			if (polyID) {
				const auto& poly = cad.mProjection.getPolynomialById(cad.idLP(it.depth() + 1), *polyID);
				SMTRAT_LOG_DEBUG("smtrat.cad", "Lifting " << s << " with " << poly);
				cad.mLifting.liftSample(it, poly, *polyID);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.cad", "Got no polynomial for " << s << ", projecting into level " << cad.idLP(it.depth() + 1) << " ...");
				SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << cad.mProjection);
				auto gotNewPolys = cad.mProjection.projectNewPolynomial();
				SMTRAT_LOG_DEBUG("smtrat.cad", "Tried to project polynomials into level " << cad.idLP(it.depth() + 1) << ", result = " << gotNewPolys);
				if (gotNewPolys.any()) {
					cad.mLifting.restoreRemovedSamples();
				} else if (cad.mProjection.empty(cad.idLP(it.depth() + 1))) {
					if (!cad.mLifting.addTrivialSample(it)) {
						cad.mLifting.removeNextSample();
					}
				} else {
					cad.mLifting.removeNextSample();
				}
			}
		}
	}
};

template<>
struct CADCore<CoreHeuristic::PreferSampling> {
	template<typename CAD>
	Answer operator()(Assignment& assignment, CAD& cad) {
		cad.mLifting.resetFullSamples();
		while (true) {
			cad.mLifting.restoreRemovedSamples();
			while (cad.mLifting.hasNextSample() || cad.mLifting.hasFullSamples()) {
				//SMTRAT_LOG_INFO("smtrat.cad", "Current Projection:" << std::endl << cad.mProjection);
				//SMTRAT_LOG_INFO("smtrat.cad", "Current lifting" << std::endl << cad.mLifting.getTree());
				Answer res = cad.checkFullSamples(assignment);
				if (res == Answer::SAT) return Answer::SAT;
				if (!cad.mLifting.hasNextSample()) break;
				
				auto it = cad.mLifting.getNextSample();
				SMTRAT_LOG_TRACE("smtrat.cad", "Queue" << std::endl << cad.mLifting.getLiftingQueue());
				Sample& s = *it;
				assert(0 <= it.depth() && it.depth() < cad.dim());
				SMTRAT_LOG_DEBUG("smtrat.cad", "Processing " << cad.mLifting.extractSampleMap(it));
				if (it.depth() > 0 && cad.checkPartialSample(it, cad.idLP(it.depth())) == Answer::UNSAT) {
					cad.mLifting.removeNextSample();
					continue;
				}
				auto polyID = cad.mProjection.getPolyForLifting(cad.idLP(it.depth() + 1), s.liftedWith());
				if (polyID) {
					const auto& poly = cad.mProjection.getPolynomialById(cad.idLP(it.depth() + 1), *polyID);
					SMTRAT_LOG_DEBUG("smtrat.cad", "Lifting " << cad.mLifting.extractSampleMap(it) << " with " << poly);
					cad.mLifting.liftSample(it, poly, *polyID);
				} else {
					SMTRAT_LOG_DEBUG("smtrat.cad", "Current lifting" << std::endl << cad.mLifting.getTree());
					SMTRAT_LOG_TRACE("smtrat.cad", "Queue" << std::endl << cad.mLifting.getLiftingQueue());
					cad.mLifting.removeNextSample();
					cad.mLifting.addTrivialSample(it);
				}
				if (CAD::SettingsT::debugStepsToTikz) {
					cad.thp.addLifting(cad.mLifting);
					cad.thp.addProjection(cad.mProjection);
					cad.thp.step();
				}
			}
			if (CAD::SettingsT::debugProjection) {
				static std::size_t counter = 0;
				counter++;
				std::ofstream out("projection_" + std::to_string(counter) + ".dot");
				out << "digraph G {" << std::endl;
				cad.mProjection.exportAsDot(out);
				out << "}" << std::endl;
				out.close();
			}
			auto r = cad.mProjection.projectNewPolynomial();
			if (r.none()) {
				SMTRAT_LOG_INFO("smtrat.cad", "Projection has finished, returning UNSAT");
				return Answer::UNSAT;
			}
			SMTRAT_LOG_INFO("smtrat.cad", "Projected into " << r << ", new projection is" << std::endl << cad.mProjection);
		}
	}
};

template<>
struct CADCore<CoreHeuristic::Interleave> {
	template<typename It>
	bool preferLifting(const It& it) {
		return it->value().isNumeric();
	}
	template<typename CAD>
	bool doProjection(CAD& cad) {
		auto r = cad.mProjection.projectNewPolynomial();
		if (r.none()) {
			SMTRAT_LOG_INFO("smtrat.cad", "Projection has finished.");
			return false;
		}
		SMTRAT_LOG_INFO("smtrat.cad", "Projected into " << r << ", new projection is" << std::endl << cad.mProjection);
		return true;
	}
	template<typename CAD>
	bool doLifting(CAD& cad) {
		if (!cad.mLifting.hasNextSample()) return false;
		auto it = cad.mLifting.getNextSample();
		SMTRAT_LOG_TRACE("smtrat.cad", "Queue" << std::endl << cad.mLifting.getLiftingQueue());
		Sample& s = *it;
		assert(0 <= it.depth() && it.depth() < cad.dim());
		SMTRAT_LOG_DEBUG("smtrat.cad", "Processing " << cad.mLifting.extractSampleMap(it));
		if (it.depth() > 0 && cad.checkPartialSample(it, cad.idLP(it.depth())) == Answer::UNSAT) {
			cad.mLifting.removeNextSample();
			return false;
		}
		auto polyID = cad.mProjection.getPolyForLifting(cad.idLP(it.depth() + 1), s.liftedWith());
		if (polyID) {
			const auto& poly = cad.mProjection.getPolynomialById(cad.idLP(it.depth() + 1), *polyID);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Lifting " << cad.mLifting.extractSampleMap(it) << " with " << poly);
			cad.mLifting.liftSample(it, poly, *polyID);
		} else {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current lifting" << std::endl << cad.mLifting.getTree());
			SMTRAT_LOG_TRACE("smtrat.cad", "Queue" << std::endl << cad.mLifting.getLiftingQueue());
			cad.mLifting.removeNextSample();
			cad.mLifting.addTrivialSample(it);
		}
		return true;
	}
	template<typename CAD>
	Answer operator()(Assignment& assignment, CAD& cad) {
		cad.mLifting.restoreRemovedSamples();
		cad.mLifting.resetFullSamples();
		while (true) {
			Answer res = cad.checkFullSamples(assignment);
			if (res == Answer::SAT) return Answer::SAT;
			if (!cad.mLifting.hasNextSample()) {
				if (!doProjection(cad)) return Answer::UNSAT;
			}
			if (preferLifting(cad.mLifting.getNextSample())) {
				doLifting(cad);
			} else {
				doProjection(cad);
				cad.mLifting.restoreRemovedSamples();
			}
		}
	}
};

template<>
struct CADCore<CoreHeuristic::EnumerateAll> {
	template<typename CAD>
	Answer operator()(Assignment& assignment, CAD& cad) {
		cad.mLifting.resetFullSamples();
		cad.mLifting.restoreRemovedSamples();
		while (true) {
			carl::Bitset gotNewPolys = cad.mProjection.projectNewPolynomial();
			if (gotNewPolys.none()) break;
		}
		while (cad.mLifting.hasNextSample()) {
			auto it = cad.mLifting.getNextSample();
			Sample& s = *it;
			SMTRAT_LOG_DEBUG("smtrat.cad", "Sample " << s << " at depth " << it.depth());
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current sample: " << cad.mLifting.printSample(it));
			assert(0 <= it.depth() && it.depth() < cad.dim());
			if (s.hasConflictWithConstraint()) {
				SMTRAT_LOG_DEBUG("smtrat.cad", "Sample " << s << " already has a conflict.");
				cad.mLifting.removeNextSample();
				continue;
			}
			auto polyID = cad.mProjection.getPolyForLifting(cad.idLP(it.depth() + 1), s.liftedWith());
			if (polyID) {
				const auto& poly = cad.mProjection.getPolynomialById(cad.idLP(it.depth() + 1), *polyID);
				SMTRAT_LOG_DEBUG("smtrat.cad", "Lifting " << s << " with " << poly);
				cad.mLifting.liftSample(it, poly, *polyID);
			} else {
				cad.mLifting.removeNextSample();
				cad.mLifting.addTrivialSample(it);
			}
		}
		std::size_t number_of_cells = 0;
		const auto& tree = cad.mLifting.getTree();
		for (auto it = tree.begin_leaf(); it != tree.end_leaf(); ++it) {
			++number_of_cells;
		}
		SMTRAT_LOG_WARN("smtrat.cad", "Got " << number_of_cells << " cells");
		
		auto assignments = cad.enumerateSolutions();
		for (const auto& a: assignments) {
			SMTRAT_LOG_WARN("smtrat.cad", "Solution: " << a);
		}
		
		if (assignments.empty()) return Answer::UNSAT;
		assignment = assignments.front();
		return Answer::SAT;
	}
};

}
}
