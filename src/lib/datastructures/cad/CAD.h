#pragma once

#include <vector>

#include <carl/core/RealAlgebraicNumberEvaluation.h>

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
		CAD(const Variables& vars):
			mVariables(vars),
			mProjection(),
			mLifting(std::move(Variables(vars.rbegin(), vars.rend())))
		{
			mProjection.reset(vars);
		}
		void addConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Adding " << c);
			mConstraints.push_back(c);
			mProjection.addPolynomial(c.lhs().toUnivariatePolynomial(mVariables[0]));
		}
		void removeConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Removing " << c);
			switch (Settings::backtracking) {
				case Backtracking::ORDERED:
					assert(mConstraints.back() == c);
					mConstraints.pop_back();
					mProjection.removePolynomial(c.lhs());
				default:
					assert(false);
			}
		}
		
		Answer checkFullSamples() {
			while (mLifting.hasFullSamples()) {
				auto it = mLifting.getNextFullSample();
				auto m = mLifting.extractSampleMap(it);
				for (const auto& c: mConstraints) {
					SMTRAT_LOG_DEBUG("smtrat.cad", "Checking " << m << " against " << c);
					auto res = carl::RealAlgebraicNumberEvaluation::evaluate(c.lhs(), m);
					bool sat = carl::evaluate(res, c.relation());
					if (!sat) return Answer::UNSAT;
				}
				SMTRAT_LOG_INFO("smtrat.cad", "Found satisfying sample " << m);
				return Answer::SAT;
			}
			return Answer::UNSAT;
		}
		
		Answer check() {
			while (true) {
				Answer res = checkFullSamples();
				if (res == Answer::SAT) return Answer::SAT;
				
				auto it = mLifting.getNextSample();
				assert(0 <= it.depth() && it.depth() < dim());
				Sample& s = *it;
				SMTRAT_LOG_DEBUG("smtrat.cad", "Sample " << s << " at depth " << it.depth());
				auto poly = mProjection.getPolyForLifting(dim() - 1 - it.depth(), s.liftedWith());
				if (poly) {
					std::cout << "Lifting " << s << " with " << *poly << std::endl;
					bool gotNewSamples = mLifting.liftSample(it, *poly);
					if (!gotNewSamples) {
						mProjection.projectNewPolynomial(dim() - 1 - it.depth());
					}
				} else {
					mLifting.removeNextSample();
				}
			}
			return Answer::UNSAT;
		}
	};
}
}
