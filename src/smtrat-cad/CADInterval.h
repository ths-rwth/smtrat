#pragma once

#include <vector>

#include "common.h"
#include "projection/Projection.h"
#include "lifting/LiftingLevel.h"
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
		LiftingLevel<Settings> mLifting;
		
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

		//@todo return type
		void getUnsatCover(Sample s) {
			if(mLifting.isSingletonCover()) {
				//@todo
			}
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
			//@todo what to initialize
			
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
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current intervals in lifting level:" << std::endl << mLifting.getUnsatIntervals());
		}
		void removeConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Removing " << c);
			auto mask = mConstraints.remove(c);
			mLifting.removedConstraint(mask);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current intervals in lifting level:" << std::endl << mLifting.getUnsatIntervals());
		}

		Answer check(Assignment& assignment, std::vector<FormulaSetT>& mis) {
			
			//@todo check

			return Answer::UNKNOWN;
		}
		
		ConflictGraph generateConflictGraph() const {
			ConflictGraph cg(mConstraints.size());
			
			//@todo generate graph

			return cg;
		}
	};
}
}
