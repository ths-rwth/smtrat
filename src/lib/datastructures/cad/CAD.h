#pragma once

#include <vector>

#include "Common.h"
#include "projection/Projection.h"
#include "lifting/LiftingTree.h"
#include "helper/CADConstraints.h"
#include "helper/SampleEvaluation.h"

namespace smtrat {
namespace cad {
	
	template<typename Settings>
	class CAD {
	private:
		Variables mVariables;
		CADConstraints<Settings::backtracking> mConstraints;
		ProjectionT<Settings> mProjection;
		LiftingTree<Settings> mLifting;
		SampleEvaluation mSampleEvaluation;
		
		// ID scheme for variables x,y,z:
		// Projection: x=0,y=1,z=2
		// Lifting: x=3,y=2,z=1,anonymous=0
		std::size_t idPL(std::size_t level) const {
			return dim() - level;
		}
		std::size_t idLP(std::size_t level) const {
			assert(level > 0);
			return dim() - level;
		}
	public:
		CAD():
			mConstraints(
				[&](const UPoly& p, std::size_t cid){ mProjection.addPolynomial(p, cid); },
				[&](const UPoly& p, std::size_t cid){ mProjection.removePolynomial(p, cid); }
			)
		{
			mProjection.setRemoveCallback([&](std::size_t level, const SampleLiftedWith& mask){
				mLifting.removeLiftedWithFlags(idPL(level) - 1, mask);
				mLifting.removeRootOfFlags(idPL(level), mask);
			});
		}
		std::size_t dim() const {
			return mVariables.size();
		}
		auto getProjection() const {
			return mProjection;
		}
		auto getLifting() const {
			return mLifting;
		}
		auto getConstraints() const {
			return mConstraints.get();
		}
		void reset(const Variables& vars) {
			mVariables = vars;
			mConstraints.reset(mVariables);
			mProjection.reset(mVariables);
			mLifting.reset(Variables(vars.rbegin(), vars.rend()));
		}
		void addConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Adding " << c);
			std::size_t id = mConstraints.add(c);
			mSampleEvaluation.addConstraint(id);
		}
		void removeConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Removing " << c);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Before removal:" << std::endl << mProjection << std::endl << mLifting.getTree());
			std::size_t id = mConstraints.remove(c);
			mSampleEvaluation.removeConstraint(id);
			SMTRAT_LOG_DEBUG("smtrat.cad", "After removal:" << std::endl << mProjection << std::endl << mLifting.getTree());
		}
		
		Answer checkFullSamples(Assignment& assignment) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Checking for full satisfying samples...");
			SMTRAT_LOG_TRACE("smtrat.cad", "Full sample queue:" << std::endl << mLifting.printFullSamples());
			while (mLifting.hasFullSamples()) {
				auto it = mLifting.getNextFullSample();
				auto m = mLifting.extractSampleMap(it);
				SMTRAT_LOG_TRACE("smtrat.cad", "Checking full sample " << m);
				assert(m.size() == it.depth());
				bool sat = true;
				for (const auto& c: mConstraints.ordered()) {
					Assignment a = m;
					// TODO: m is cleared by the call to evaluate() ... 
					auto res = carl::RealAlgebraicNumberEvaluation::evaluate(c.first.lhs(), a);
					SMTRAT_LOG_TRACE("smtrat.cad", "Evaluating " << c.first.lhs() << " on " << m << " -> " << res);
					sat = sat && carl::evaluate(res, c.first.relation());
					if (!sat) break;
				}
				if (sat) {
					SMTRAT_LOG_INFO("smtrat.cad", "Found satisfying sample " << m);
					assignment = m;
					return Answer::SAT;
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.cad", "No full satisfying sample found.");
			return Answer::UNSAT;
		}
		
		Answer check(Assignment& assignment) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Checking constraints:" << std::endl << mConstraints);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			mLifting.resetFullSamples();
			mLifting.restoreRemovedSamples();
			while (true) {
				SMTRAT_LOG_DEBUG("smtrat.cad", "Current sample tree:" << std::endl << mLifting.getTree());
				Answer res = checkFullSamples(assignment);
				if (res == Answer::SAT) return Answer::SAT;
				
				if (!mLifting.hasNextSample()) {
					SMTRAT_LOG_DEBUG("smtrat.cad", "There is no sample to be lifted.");
					break;
				}
				auto it = mLifting.getNextSample();
				Sample& s = *it;
				SMTRAT_LOG_DEBUG("smtrat.cad", "Sample " << s << " at depth " << it.depth());
				SMTRAT_LOG_DEBUG("smtrat.cad", "Current sample: " << mLifting.printSample(it));
				assert(0 <= it.depth() && it.depth() < dim());
				auto polyID = mProjection.getPolyForLifting(idLP(it.depth() + 1), s.liftedWith());
				if (polyID) {
					const auto& poly = mProjection.getPolynomialById(idLP(it.depth() + 1), *polyID);
					SMTRAT_LOG_DEBUG("smtrat.cad", "Lifting " << s << " with " << poly);
					mLifting.liftSample(it, poly, *polyID);
				} else {
					SMTRAT_LOG_DEBUG("smtrat.cad", "Got no polynomial for " << s << ", projecting into level " << (dim() - 1 - it.depth()) << " ...");
					bool gotNewPolys = mProjection.projectNewPolynomial(idLP(it.depth() + 1));
					if (gotNewPolys) {
						SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
						mLifting.restoreRemovedSamples();
					} else if (mProjection.empty(idLP(it.depth() + 1))) {
						if (!mLifting.addTrivialSample(it)) {
							mLifting.removeNextSample();
						}
					} else {
						mLifting.removeNextSample();
					}
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current sampletree:" << std::endl << mLifting.getTree());
			return Answer::UNSAT;
		}
	};
}
}
