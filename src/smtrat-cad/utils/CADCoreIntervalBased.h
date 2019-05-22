#pragma once

#include "../common.h"
#include "../Settings.h"

#include <smtrat-cad/lifting/Sample.h>
#include <smtrat-cad/lifting/LiftingLevel.h>

namespace smtrat {
namespace cad {

template<CoreIntervalBasedHeuristic CH>
struct CADCoreIntervalBased {};

template<>
struct CADCoreIntervalBased<CoreIntervalBasedHeuristic::PreferLifting> {
	template<typename CADIntervalBased>
	bool doProjection(CADIntervalBased& cad) {
		auto r = cad.mProjection.projectNewPolynomial();
		if (r.none()) {
			SMTRAT_LOG_INFO("smtrat.cad", "Projection has finished.");
			return false;
		}
		SMTRAT_LOG_INFO("smtrat.cad", "Projected into " << r << ", new projection is" << std::endl << cad.mProjection);
		return true;
	}
	template<typename CADIntervalBased>
	bool doLifting(CADIntervalBased& cad) {
		//@todo is mLifting.back() applicable here? maybe specify lifting level or iterator instead for recursion
        // no lifting is possible if an unsat cover was found
		if (cad.mLifting.back().isUnsatCover()) return false;

        while(!cad.mLifting.back().isUnsatCover()) {
            // compute a new sample outside of known unsat intervals
            auto s = cad.mLifting.back().chooseSample();
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

	/**
	 * @param cad 	CAD class
	 * @param dim	dimension of current lifting level
	 * @returns true if SAT, false if UNSAT
	 * @returns in UNSAT case: intervals forming the unsat cover
	 * @returns in SAT case: vector of samples as satisfying witness (ordered from lowest to highest dimension)
	 */
	template<typename CADIntervalBased>
	std::tuple<bool, std::vector<CADInterval>, std::vector<Sample>> getUnsatCover(
		CADIntervalBased& cad, std::vector<Sample> samples) {

		// get the current dimension
		int dim = samples.size();
		// there should be lifting levels for all former dimensions and none for the current one
		assert(cad.mLifting.size() == dim);
		//@todo initialize new lifting level with conss, get intervals
		cad.mLifting.push_back(new LiftingLevel());

        // no lifting is possible if an unsat cover was found
		if (cad.mLifting.back().isUnsatCover()) return false;

        while(!cad.mLifting.back().isUnsatCover()) {
            // compute a new sample outside of known unsat intervals
            auto s = cad.mLifting.back().chooseSample();
            SMTRAT_LOG_TRACE("smtrat.cad", "Next sample" << std::endl << s);
			samples.push_back(s);
			// have we reached full dimension yet?
			if(samples.size() == cad.dim())
				return new std::tuple<bool, std::vector<CADInterval>, std::vector<Sample>>(true, new std::vector<CADInterval>, samples);

			auto samplecheck = getUnsatCover(cad, samples);
            //@todo check whether all former levels + new sample are sat, if true return sat

			// if the result was sat, return the resulting samples as witnesses
			if(std::get<0>(samplecheck) == true) 
				return new std::tuple<bool, std::vector<CADInterval>, std::vector<Sample>>(true, new std::vector<CADInterval>, std::get<2>(samplecheck));
			else
			{
				auto r = cad.construct_characterization(samples); //@todo
				CADInterval i = cad.interval_from_characterization(samples, std::get<1>(samplecheck)); //@todo
				cad.mLifting.back().addUnsatInterval(i);
			}
        }
		return true;
	}
	template<typename CADIntervalBased>
	Answer operator()(Assignment& assignment, CADIntervalBased& cad) {
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
