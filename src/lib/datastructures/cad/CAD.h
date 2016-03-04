#pragma once

#include <vector>

#include "Common.h"
#include "projection/Projection.h"
#include "lifting/LiftingTree.h"

namespace smtrat {
namespace cad {
	
	template<typename Settings>
	class CAD {
	private:
		Variables mVariables;
		ProjectionT<Settings> mProjection;
		LiftingTree<Settings> mLifting;
		std::vector<ConstraintT> mConstraints;
		
		std::size_t dim() const {
			return mVariables.size();
		}
	public:
		void reset(const Variables& vars) {
			mVariables = vars;
			mProjection.reset(mVariables);
			mLifting.reset(Variables(vars.rbegin(), vars.rend()));
		}
		void addConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Adding " << c);
			assert(!mVariables.empty());
			mConstraints.push_back(c);
			mProjection.addPolynomial(c.lhs().toUnivariatePolynomial(mVariables.front()));
		}
		void removeConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Removing " << c);
			assert(!mVariables.empty());
			switch (Settings::backtracking) {
				case Backtracking::ORDERED:
					assert(mConstraints.back() == c);
					mConstraints.pop_back();
					mProjection.removePolynomial(c.lhs().toUnivariatePolynomial(mVariables.front()));
				default:
					assert(false);
			}
		}
		
		Answer checkFullSamples(Assignment& assignment) {
			SMTRAT_LOG_TRACE("smtrat.cad", "Full sample queue:" << std::endl << mLifting.printFullSamples());
			while (mLifting.hasFullSamples()) {
				auto it = mLifting.getNextFullSample();
				auto m = mLifting.extractSampleMap(it);
				assert(m.size() == it.depth());
				for (const auto& c: mConstraints) {
					SMTRAT_LOG_DEBUG("smtrat.cad", "Checking " << m << " against " << c);
					// TODO: m is cleared by the call to evaluate() ... 
					auto assignment = m;
					auto res = carl::RealAlgebraicNumberEvaluation::evaluate(c.lhs(), assignment);
					bool sat = carl::evaluate(res, c.relation());
					if (!sat) return Answer::UNSAT;
				}
				SMTRAT_LOG_INFO("smtrat.cad", "Found satisfying sample " << m);
				assignment = m;
				return Answer::SAT;
			}
			return Answer::UNSAT;
		}
		
		Answer check(Assignment& assignment) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			while (true) {
				Answer res = checkFullSamples(assignment);
				if (res == Answer::SAT) return Answer::SAT;
				
				if (!mLifting.hasNextSample()) break;
				auto it = mLifting.getNextSample();
				assert(0 <= it.depth() && it.depth() < dim());
				Sample& s = *it;
				SMTRAT_LOG_DEBUG("smtrat.cad", "Sample " << s << " at depth " << it.depth());
				SMTRAT_LOG_DEBUG("smtrat.cad", "Current sample: " << mLifting.printSample(it));
				auto poly = mProjection.getPolyForLifting(dim() - 1 - it.depth(), s.liftedWith());
				if (poly) {
					SMTRAT_LOG_DEBUG("smtrat.cad", "Lifting " << s << " with " << *poly);
					mLifting.liftSample(it, *poly);
				} else {
					SMTRAT_LOG_DEBUG("smtrat.cad", "Got no polynomial for " << s << ", projecting into level " << (dim() - 1 - it.depth()) << " ...");
					bool gotNewPolys = mProjection.projectNewPolynomial(dim() - 1 - it.depth());
					if (gotNewPolys) {
						mLifting.restoreRemovedSamples();
					} else {
						mLifting.removeNextSample();
					}
				}
			}
			return Answer::UNSAT;
		}
	};
}
}
