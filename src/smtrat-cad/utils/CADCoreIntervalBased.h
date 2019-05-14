#pragma once

#include "../common.h"
#include "../Settings.h"

#include <smtrat-cad/lifting/Sample.h>

namespace smtrat {
namespace cad {

template<CoreIntervalBasedHeuristic CH>
struct CADCoreIntervalBased {};

template<>
struct CADCoreIntervalBased<CoreIntervalBasedHeuristic::PreferLifting> {
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
        // no lifting is possible if an unsat cover was found
		if (cad.mLifting.isUnsatCover()) return false;

        while(!cad.mLifting.isUnsatCover()) {
            // compute a new sample outside of known unsat intervals
            auto s = cad.mLifting.chooseSample();
            SMTRAT_LOG_TRACE("smtrat.cad", "Next sample" << std::endl << s);
            //@todo check whether all former levels + new sample are sat, if true return sat

            auto intervals = cad.mLifting.getUnsatIntervals();
		    SMTRAT_LOG_TRACE("smtrat.cad", "Current intervals" << std::endl << intervals);
        }

        //@todo this is code from CADCore, adapt
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
        //@todo there should probably be a different preference order here?!
		cad.mLifting.restoreRemovedSamples();
		cad.mLifting.resetFullSamples();
		while (true) {
			Answer res = cad.checkFullSamples(assignment);
			if (res == Answer::SAT) return Answer::SAT;
			if (!cad.mLifting.hasNextSample()) {
				if (!doProjection(cad)) return Answer::UNSAT;
				cad.mLifting.restoreRemovedSamples();
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

}
}
