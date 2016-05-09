#pragma once

#include <vector>

#include "Common.h"
#include "projection/Projection.h"
#include "lifting/LiftingTree.h"
#include "helper/CADConstraints.h"
#include "helper/CADCore.h"
#include "helper/ConflictGraph.h"
#include "helper/MISGeneration.h"

namespace smtrat {
namespace cad {
	
	template<typename Settings>
	class CAD {
		template<CoreHeuristic CH>
		friend struct CADCore;
	private:
		Variables mVariables;
		CADConstraints<Settings::backtracking> mConstraints;
		ProjectionT<Settings> mProjection;
		LiftingTree<Settings> mLifting;
		
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
			),
			mLifting(mConstraints)
		{
			mProjection.setRemoveCallback([&](std::size_t level, const SampleLiftedWith& mask){
				mLifting.removedPolynomialsFromLevel(idPL(level), mask);
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
			return mConstraints.indexed();
		}
		void reset(const Variables& vars) {
			mVariables = vars;
			mConstraints.reset(mVariables);
			mProjection.reset(mVariables);
			mLifting.reset(Variables(vars.rbegin(), vars.rend()));
		}
		void addConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Adding " << c);
			mConstraints.add(c);
		}
		void removeConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Removing " << c);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Before removal:" << std::endl << mProjection << std::endl << mLifting.getTree());
			std::size_t id = mConstraints.remove(c);
			mLifting.removedConstraint(Bitset(id));
			SMTRAT_LOG_DEBUG("smtrat.cad", "After removal:" << std::endl << mProjection << std::endl << mLifting.getTree());
		}
		
		template<typename ConstraintIt>
		bool evaluateSample(Sample& sample, const ConstraintIt& constraint, Assignment& assignment) const {
			std::size_t cid = constraint.second;
			if (sample.evaluatedWith().test(cid)) {
				return sample.evaluationResult().test(cid);
			}
			auto res = carl::RealAlgebraicNumberEvaluation::evaluate(constraint.first.lhs(), assignment);
			bool evalResult = carl::evaluate(res, constraint.first.relation());
			SMTRAT_LOG_TRACE("smtrat.cad", "Evaluating " << constraint.first.lhs() << " " << constraint.first.relation() << " 0 on " << assignment << " -> " << evalResult);
			sample.evaluatedWith().set(cid, true);
			sample.evaluationResult().set(cid, evalResult);
			return evalResult;
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
					sat = sat && evaluateSample(*it, c, a);
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
			if (mConstraints.bounds().isConflicting()) {
				SMTRAT_LOG_DEBUG("smtrat.cad", "Trivially unsat due to bounds.");
				return Answer::UNSAT;
			}
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			CADCore<Settings::coreHeuristic> cad;
			auto res = cad(assignment, *this);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current sampletree:" << std::endl << mLifting.getTree());
			return res;
		}
		
		ConflictGraph generateConflictGraph() const {
			ConflictGraph cg(mConstraints.size());
			for (const auto& s: mLifting.getTree()) {
				if (s.hasConflictWithConstraint()) {
					cg.addSample(s);
				}
			}
			return cg;
		}
		
		void generateInfeasibleSubsets(std::vector<FormulaSetT>& mis) const {
			cad::MISGeneration<Settings::misHeuristic> generator;
			generator(*this, mis);
		}
	};
}
}
