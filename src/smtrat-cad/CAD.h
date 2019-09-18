#pragma once

#include <vector>

#include <carl-covering/carl-covering.h>

#include "common.h"
#include "projection/Projection.h"
#include "lifting/LiftingTree.h"
#include "utils/CADConstraints.h"
#include "utils/CADCore.h"
#include "utils/ConflictGraph.h"
#include "utils/MISGeneration.h"
#include "debug/TikzHistoryPrinter.h"

namespace smtrat {
namespace cad {
	
	template<typename Settings>
	class CAD {
	public:
		template<CoreHeuristic CH>
		friend struct CADCore;
		using SettingsT = Settings;
	private:
		std::vector<carl::Variable> mVariables;
		CADConstraints<Settings::backtracking> mConstraints;
		ProjectionT<Settings> mProjection;
		LiftingTree<Settings> mLifting;
		
		// ID scheme for variables x,y,z:
		// Projection: x=1,y=2,z=3
		// Lifting: x=3,y=2,z=1,anonymous=0
		std::size_t idPL(std::size_t level) const {
			assert(level > 0 && level <= dim());
			return dim() - level + 1;
		}
		std::size_t idLP(std::size_t level) const {
			assert(level > 0 && level <= dim());
			return dim() - level + 1;
		}
	public:
		debug::TikzHistoryPrinter thp;
		CAD():
			mConstraints(
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.addPolynomial(projection::normalize(p), cid, isBound); },
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.addEqConstraint(projection::normalize(p), cid, isBound); },
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.removePolynomial(projection::normalize(p), cid, isBound); }
			),
			mProjection(mConstraints),
			mLifting(mConstraints)
		{
			mProjection.setRemoveCallback([&](std::size_t level, const SampleLiftedWith& mask){
				mLifting.removedPolynomialsFromLevel(idPL(level), mask);
			});
			
			if (Settings::debugStepsToTikz) {
				thp.configure<debug::TikzTreePrinter>("Lifting");
				thp.configure<debug::TikzDAGPrinter>("Projection");
			}
		}
		~CAD() {
			if (Settings::debugStepsToTikz) {
				thp.layout();
				thp.writeTo("cad_debug.tex");
			}
		}
		std::size_t dim() const {
			return mVariables.size();
		}
		const auto& getVariables() const {
			return mVariables;
		}
		const auto& getProjection() const {
			return mProjection;
		}
		const auto& getLifting() const {
			return mLifting;
		}
		const auto& getConstraints() const {
			return mConstraints.indexed();
		}
		const auto& getConstraintMap() const {
			return mConstraints.ordered();
		}
		bool isIdValid(std::size_t id) const {
			return mConstraints.valid(id);
		}
		const auto& getBounds() const {
			return mConstraints.bounds();
		}
		void reset(const std::vector<carl::Variable>& vars) {
			mVariables = vars;
			mConstraints.reset(mVariables);
			mProjection.reset();
			mLifting.reset(std::vector<carl::Variable>(vars.rbegin(), vars.rend()));
		}
		void addConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Adding " << c);
			mConstraints.add(c);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current sampletree:" << std::endl << mLifting.getTree());
		}
		void removeConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Removing " << c);
			auto mask = mConstraints.remove(c);
			mLifting.removedConstraint(mask);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current sampletree:" << std::endl << mLifting.getTree());
		}
		
		template<typename ConstraintIt>
		bool evaluateSample(Sample& sample, const ConstraintIt& constraint, Assignment& assignment) const {
			std::size_t cid = constraint.second;
			SMTRAT_LOG_TRACE("smtrat.cad.lifting", "Evaluating " << cid << " / " << constraint.first << " on " << assignment);
			SMTRAT_LOG_TRACE("smtrat.cad.lifting", "Sample was evaluated: " << sample.evaluatedWith() << " / " << sample.evaluationResult());
			if (sample.evaluatedWith().test(cid)) {
				return sample.evaluationResult().test(cid);
			}
			bool evalResult = carl::RealAlgebraicNumberEvaluation::evaluate(constraint.first, assignment);
			SMTRAT_LOG_TRACE("smtrat.cad.lifting", "Evaluating " << constraint.first << " on " << assignment << " -> " << evalResult);
			sample.evaluatedWith().set(cid, true);
			sample.evaluationResult().set(cid, evalResult);
			return evalResult;
		}
		
		std::vector<Assignment> enumerateSolutions() {
			std::vector<Assignment> res;
			SMTRAT_LOG_TRACE("smtrat.cad", "Enumerating satisfying samples...");
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
					SMTRAT_LOG_DEBUG("smtrat.cad", "Found satisfying sample " << m);
					res.emplace_back(m);
				}
			}
			return res;
		}

		Answer checkFullSamples(Assignment& assignment) {
			if (!mLifting.hasFullSamples()) return Answer::UNSAT;
			SMTRAT_LOG_TRACE("smtrat.cad", "Checking for full satisfying samples...");
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
					SMTRAT_LOG_DEBUG("smtrat.cad", "Found satisfying sample " << m);
					assignment = m;
					return Answer::SAT;
				}
			}
			SMTRAT_LOG_TRACE("smtrat.cad", "No full satisfying sample found.");
			return Answer::UNSAT;
		}
		
		template<typename Iterator>
		Answer checkPartialSample(Iterator& it, std::size_t level) {
			SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "Checking partial sample " << *it << " against level " << level);
			Answer answer = Answer::SAT;
			if (it->hasConflictWithConstraint()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "\tAlready has conflict...");
				answer = Answer::UNSAT;
			}
			for (const auto& c: mConstraints.ordered()) {
				if (mConstraints.level(c.second) != level) continue;
				auto a = mLifting.extractSampleMap(it);
				if (!evaluateSample(*it, c, a)) {
					SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "\tConflicts with " << c.first);
					answer = Answer::UNSAT;
				}
			}
			return answer;
		}

		Answer check(Assignment& assignment, std::vector<FormulaSetT>& mis) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Checking constraints:" << std::endl << mConstraints);
			if (mConstraints.checkForTrivialConflict(mis)) {
				return Answer::UNSAT;
			}
			SMTRAT_LOG_INFO("smtrat.cad", "Current projection:" << std::endl << mProjection);
			CADCore<Settings::coreHeuristic> cad;
			auto res = cad(assignment, *this);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Result: " << res);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current sampletree:" << std::endl << mLifting.getTree());
			if (res == Answer::UNSAT) {
				cad::MISGeneration<Settings::misHeuristic> generator;
				generator(*this, mis);
			}
			return res;
		}
		
		ConflictGraph generateConflictGraph() const {
			ConflictGraph cg(mConstraints.size());
			for (auto it = mLifting.getTree().begin_preorder(); it != mLifting.getTree().end_preorder();) {
				if (it->hasConflictWithConstraint()) {
					// Skip subtrees of already conflicting samples
					SMTRAT_LOG_TRACE("smtrat.cad.mis", "Adding sample " << *it);
					cg.addSample(*it);
					it.skipChildren();
				} else {
					it++;
				}
				for (std::size_t id = 0; id < mConstraints.size(); id++) {
					if (!mConstraints.valid(id)) {
						SMTRAT_LOG_TRACE("smtrat.cad.mis", "Invalid constraint: " << id << ", cur graph:" << std::endl << cg);
					}
					assert(mConstraints.valid(id) || cg.coveredSamples(id) == 0);
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.mis", "Resulting conflict graph " << cg);
			return cg;
		}
		
		auto generateCovering() const {
			carl::covering::TypedSetCover<ConstraintT> cover;
			SMTRAT_LOG_DEBUG("smtrat.cad.mis", "Current lifting tree: " << std::endl << mLifting.getTree());
			carl::IDPool idpool;
			for (auto it = mLifting.getTree().begin_preorder(); it != mLifting.getTree().end_preorder();) {
				auto constraints = it->getConflictingConstraints();
				if (constraints.any()) {
					auto sid = idpool.get();
					for (auto cid: constraints) {
						SMTRAT_LOG_DEBUG("smtrat.cad.mis", sid << " " << *it << " vs. " << cid);
						cover.set(mConstraints[cid], sid);
					}
					it.skipChildren();
				} else {
					it++;
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.mis", "Resulting covering " << cover);
			return cover;
		}
	};
}
}
